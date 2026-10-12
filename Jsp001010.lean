import Mathlib

open Finset Real Filter Topology BigOperators Nat

noncomputable section

/-- The number of congruences `m ≡ a n (mod n)` with `1 ≤ n ≤ x` satisfied by `m`. -/
def coverCount (x : ℕ) (a : ℕ → ℕ) (m : ℕ) : ℕ :=
  ((Icc 1 x).filter fun n => m ≡ a n [MOD n]).card

/-- `goodAssign x k` : there is an assignment of residue classes such that every
`1 ≤ m ≤ x` satisfies at least `k` of the congruences. -/
def goodAssign (x k : ℕ) : Prop :=
  ∃ a : ℕ → ℕ, ∀ m ∈ Icc 1 x, k ≤ coverCount x a m

/-- `F x` : the largest `k` such that some choice of residue classes `aₙ mod n`
(`n ≤ x`) covers every `m ≤ x` at least `k` times. -/
noncomputable def F (x : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (goodAssign x) x

end

/-! ## Basic facts -/

lemma coverCount_le (x : ℕ) (a : ℕ → ℕ) (m : ℕ) : coverCount x a m ≤ x := by
  unfold coverCount
  calc ((Icc 1 x).filter _).card ≤ (Icc 1 x).card := card_filter_le _ _
    _ = x := by simp

lemma goodAssign_zero (x : ℕ) : goodAssign x 0 :=
  ⟨fun _ => 0, fun _m _ => Nat.zero_le _⟩

/-- If some assignment covers everything `k` times and `k ≤ x`, then `k ≤ F x`. -/
lemma le_F (x k : ℕ) (hk : k ≤ x) (h : goodAssign x k) : k ≤ F x := by
  classical
  simpa [F] using Nat.le_findGreatest (P := goodAssign x) hk h

/-- `F x` itself is witnessed by an assignment. -/
lemma goodAssign_F (x : ℕ) : goodAssign x (F x) := by
  classical
  simpa [F] using
    Nat.findGreatest_spec (P := goodAssign x) (Nat.zero_le x) (goodAssign_zero x)

lemma F_le (x : ℕ) : F x ≤ x := by
  classical
  simpa [F] using Nat.findGreatest_le (P := goodAssign x) x

/-- Cover count as a sum of indicators. -/
lemma coverCount_eq_sum (x : ℕ) (a : ℕ → ℕ) (m : ℕ) :
    (coverCount x a m : ℝ) = ∑ n ∈ Icc 1 x, (if m ≡ a n [MOD n] then (1:ℝ) else 0) := by
  rw [coverCount, ← Finset.sum_boole]

/-! ## Upper bound `F x ≤ H_x + 1` -/

/-- For a fixed modulus `n ≥ 1`, at most `x/n + 1` values of `m ∈ [1,x]` lie in a
single residue class mod `n`. -/
lemma card_modEq_le (x n r : ℕ) (hn : 1 ≤ n) :
    ((Icc 1 x).filter fun m => m ≡ r [MOD n]).card ≤ x / n + 1 := by
  have hn0 : 0 < n := hn
  suffices h : ((Icc 1 x).filter fun m => m ≡ r [MOD n]).card ≤ (Icc 0 (x / n)).card by
    rwa [Nat.card_Icc, Nat.sub_zero] at h
  apply Finset.card_le_card_of_injOn (fun m => m / n)
  · intro m hm
    rw [Finset.mem_coe, mem_Icc]
    exact ⟨Nat.zero_le _,
      Nat.div_le_div_right (mem_Icc.mp (mem_filter.mp hm).1).2⟩
  · intro m₁ hm₁ m₂ hm₂ heq
    have heq' : m₁ / n = m₂ / n := heq
    have h1 : m₁ % n = m₂ % n :=
      (mem_filter.mp hm₁).2.trans (mem_filter.mp hm₂).2.symm
    calc m₁ = n * (m₁ / n) + m₁ % n := (Nat.div_add_mod m₁ n).symm
      _ = n * (m₂ / n) + m₂ % n := by rw [heq', h1]
      _ = m₂ := Nat.div_add_mod m₂ n

/-- Total coverage summed over `m ≤ x` is at most `x·H_x + x`. -/
lemma sum_coverCount_le (x : ℕ) (a : ℕ → ℕ) :
    (∑ m ∈ Icc 1 x, (coverCount x a m : ℝ)) ≤ x * (∑ n ∈ Icc 1 x, (n : ℝ)⁻¹) + x := by
  have key : ∀ n ∈ Icc 1 x,
      (∑ m ∈ Icc 1 x, (if m ≡ a n [MOD n] then (1:ℝ) else 0)) ≤ (x:ℝ)/n + 1 := by
    intro n hn
    have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
    rw [Finset.sum_boole]
    have h := card_modEq_le x n (a n) hn1
    calc (((Icc 1 x).filter fun m => m ≡ a n [MOD n]).card : ℝ)
        ≤ ((x / n : ℕ) : ℝ) + 1 := by exact_mod_cast h
      _ ≤ (x:ℝ)/n + 1 := by
        have hcd := (Nat.cast_div_le : ((x / n : ℕ) : ℝ) ≤ (x : ℝ) / (n : ℝ))
        linarith
  calc ∑ m ∈ Icc 1 x, (coverCount x a m : ℝ)
      = ∑ m ∈ Icc 1 x, ∑ n ∈ Icc 1 x, (if m ≡ a n [MOD n] then (1:ℝ) else 0) := by
        exact sum_congr rfl fun m _ => coverCount_eq_sum x a m
    _ = ∑ n ∈ Icc 1 x, ∑ m ∈ Icc 1 x, (if m ≡ a n [MOD n] then (1:ℝ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ n ∈ Icc 1 x, ((x:ℝ)/n + 1) := sum_le_sum key
    _ = x * (∑ n ∈ Icc 1 x, (n : ℝ)⁻¹) + x := by
        rw [sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]; apply sum_congr rfl; intro n _; rw [div_eq_mul_inv]
        · rw [sum_const, Nat.card_Icc]; simp

/-- **Upper bound** (pigeonhole): `F x ≤ H_x + 1` where `H_x = ∑ 1/n`. -/
theorem F_upper (x : ℕ) (hx : 1 ≤ x) :
    (F x : ℝ) ≤ ∑ n ∈ Icc 1 x, (n : ℝ)⁻¹ + 1 := by
  obtain ⟨a, ha⟩ := goodAssign_F x
  have hsum := sum_coverCount_le x a
  have hmin : (x : ℝ) * (F x : ℝ) ≤ ∑ m ∈ Icc 1 x, (coverCount x a m : ℝ) := by
    calc (x : ℝ) * F x = ∑ m ∈ Icc 1 x, (F x : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc]; simp
      _ ≤ _ := sum_le_sum fun m hm => by exact_mod_cast ha m hm
  have hxr : (0 : ℝ) < x := by exact_mod_cast hx
  have h2 : (x : ℝ) * F x ≤ x * ((∑ n ∈ Icc 1 x, (n : ℝ)⁻¹) + 1) := by
    have := hmin.trans hsum
    ring_nf at this ⊢; linarith
  exact le_of_mul_le_mul_left h2 hxr

/-! ## Harmonic bounds -/

/-- For `n ≥ 1`, `1/(n+1) ≤ log(n+1) − log n` (telescoping step). -/
lemma inv_succ_le_log_sub_log (n : ℕ) (hn : 1 ≤ n) :
    ((n + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log (n + 1) - Real.log n := by
  have h1 : (0 : ℝ) < (n : ℝ) / (n + 1) := by positivity
  have h := Real.log_le_sub_one_of_pos h1
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h2 : (n : ℝ) / (n + 1) - 1 = -(((n + 1 : ℕ) : ℝ)⁻¹) := by
    field_simp
    push_cast
    ring
  rw [h2] at h
  linarith

/-- For `n ≥ 1`, `log(n+1) − log n ≤ 1/n` (telescoping step). -/
lemma log_sub_log_le_inv (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1) - Real.log n ≤ (n : ℝ)⁻¹ := by
  have h1 : (0 : ℝ) < ((n : ℝ) + 1) / n := by positivity
  have h := Real.log_le_sub_one_of_pos h1
  rw [Real.log_div (by positivity) (by positivity)] at h
  have h2 : ((n : ℝ) + 1) / n - 1 = (n : ℝ)⁻¹ := by field_simp; ring
  rw [h2] at h
  exact h

lemma Icc_one_succ (N : ℕ) : Icc 1 (N + 1) = insert (N + 1) (Icc 1 N) := by
  ext m; simp only [mem_Icc, mem_insert]; omega

/-- `H_N ≤ 1 + log N` for `N ≥ 1`. -/
lemma harmonic_le (N : ℕ) : 1 ≤ N →
    ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ ≤ 1 + Real.log N := by
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro hN
    rcases Nat.eq_zero_or_pos N with rfl | hNpos
    · simp
    · have ihn := ih (Nat.succ_le_of_lt hNpos)
      rw [Icc_one_succ, sum_insert (by simp)]
      have hstep := inv_succ_le_log_sub_log N (Nat.succ_le_of_lt hNpos)
      have h2 := add_le_add ihn hstep
      push_cast at h2 ⊢
      linarith

/-- `log (N+1) ≤ H_N`. -/
lemma log_le_harmonic (N : ℕ) :
    Real.log (N + 1) ≤ ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Icc_one_succ, sum_insert (by simp)]
    have hstep := log_sub_log_le_inv (N + 1) (Nat.le_add_left 1 N)
    have h2 := add_le_add ih hstep
    push_cast at h2 ⊢
    linarith

/-! ## Lower bound: counting over assignments -/

/-- Assignments on `[1,N]`: a residue class in `Fin n` for each modulus `n`. -/
abbrev Assign (N : ℕ) := ∀ i : ↥(Icc 1 N), Fin i.1

noncomputable instance : DecidableEq (Assign N) := Classical.decEq _

instance nonemptyAssign (N : ℕ) : Nonempty (Assign N) :=
  ⟨fun i => ⟨0, by have := (mem_Icc.mp i.2).1; omega⟩⟩

/-- For an assignment `f` on `[1,N]`, the number of moduli covering `m`. -/
def coverLow (N : ℕ) (f : Assign N) (m : ℕ) : ℕ :=
  (univ.filter fun i : ↥(Icc 1 N) => (f i : ℕ) = m % i.1).card

lemma coverLow_eq_sum (N : ℕ) (f : Assign N) (m : ℕ) :
    (coverLow N f m : ℝ) = ∑ i : ↥(Icc 1 N), (if (f i : ℕ) = m % i.1 then (1:ℝ) else 0) := by
  rw [coverLow, ← Finset.sum_boole]

set_option maxHeartbeats 400000 in
/-- **Moment generating sum.** Summing `exp(-λ·X_m)` over all assignments on `[1,N]`
factors as `∏ (n - 1 + exp(-λ))`. -/
lemma sum_exp_neg_coverLow (N : ℕ) (m : ℕ) (lam : ℝ) :
    ∑ f : Assign N, Real.exp (-lam * (coverLow N f m : ℝ))
      = ∏ i : ↥(Icc 1 N), ((i.1 : ℝ) - 1 + Real.exp (-lam)) := by
  classical
  have hprod : ∀ f : Assign N, Real.exp (-lam * (coverLow N f m : ℝ))
      = ∏ i : ↥(Icc 1 N), Real.exp (-lam * (if (f i : ℕ) = m % i.1 then (1:ℝ) else 0)) := by
    intro f
    rw [coverLow_eq_sum, Finset.mul_sum, Real.exp_sum]
  calc ∑ f : Assign N, Real.exp (-lam * (coverLow N f m : ℝ))
      = ∑ f : Assign N, ∏ i : ↥(Icc 1 N),
          Real.exp (-lam * (if (f i : ℕ) = m % i.1 then (1:ℝ) else 0)) :=
        sum_congr rfl fun f _ => hprod f
    _ = ∏ i : ↥(Icc 1 N), ∑ k : Fin i.1,
          Real.exp (-lam * (if (k : ℕ) = m % i.1 then (1:ℝ) else 0)) :=
        (Fintype.prod_sum fun (i : ↥(Icc 1 N)) (k : Fin i.1) =>
          Real.exp (-lam * (if (k : ℕ) = m % i.1 then (1:ℝ) else 0))).symm
    _ = ∏ i : ↥(Icc 1 N), ((i.1 : ℝ) - 1 + Real.exp (-lam)) := by
        apply prod_congr rfl
        intro i _
        have hi : 0 < i.1 := (mem_Icc.mp i.2).1
        set k₀ : Fin i.1 := ⟨m % i.1, Nat.mod_lt _ hi⟩ with hk₀
        rw [sum_eq_add_sum_sdiff_singleton_of_mem (mem_univ k₀)]
        have hrest : ∑ k ∈ univ \ {k₀},
            Real.exp (-lam * (if (k : ℕ) = m % i.1 then (1:ℝ) else 0)) = (i.1 - 1 : ℝ) := by
          have he : ∀ k ∈ univ \ {k₀},
              Real.exp (-lam * (if (k : ℕ) = m % i.1 then (1:ℝ) else 0)) = 1 := by
            intro k hk
            have hne : ¬((k : ℕ) = m % i.1) := by
              intro hkm
              have hkk : k = k₀ := Fin.ext hkm
              exact (mem_sdiff.mp hk).2 (mem_singleton.mpr hkk)
            rw [ite_eq_right hne]; simp
          rw [sum_congr rfl he, sum_const, Finset.card_sdiff, Finset.inter_univ,
            Finset.card_singleton, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            mul_one, Nat.cast_sub hi, Nat.cast_one]
        rw [hrest]
        have hk0' : (k₀ : ℕ) = m % i.1 := rfl
        rw [ite_eq_left hk0', mul_one]
        ring

/-- **Chernoff-style count.** At most `|Assign N| · exp(λK + H_N·(e^{-λ} - 1))`
assignments cover `m` at most `K` times. -/
lemma card_bad_le (N : ℕ) (m : ℕ) (lam K : ℝ) (hlam : 0 ≤ lam) :
    ((univ.filter fun f : Assign N => (coverLow N f m : ℝ) ≤ K).card : ℝ)
      ≤ (Fintype.card (Assign N) : ℝ) *
        Real.exp (lam * K + (∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1)) := by
  classical
  have hS : (0:ℝ) < Fintype.card (Assign N) := by exact_mod_cast Fintype.card_pos
  -- `card_bad · e^{-λK} ≤ Σ_f e^{-λX} = ∏ (n-1+e^{-λ})`
  have h1 : ((univ.filter fun f : Assign N => (coverLow N f m : ℝ) ≤ K).card : ℝ)
        * Real.exp (-lam * K)
      ≤ ∏ i : ↥(Icc 1 N), ((i.1 : ℝ) - 1 + Real.exp (-lam)) := by
    calc ((univ.filter fun f : Assign N => (coverLow N f m : ℝ) ≤ K).card : ℝ)
          * Real.exp (-lam * K)
        = ∑ f ∈ univ.filter (fun f : Assign N => (coverLow N f m : ℝ) ≤ K),
            Real.exp (-lam * K) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ univ.filter (fun f : Assign N => (coverLow N f m : ℝ) ≤ K),
            Real.exp (-lam * (coverLow N f m : ℝ)) := by
          apply sum_le_sum; intro f hf
          have hfK : (coverLow N f m : ℝ) ≤ K := by simpa using hf
          have : -lam * (coverLow N f m : ℝ) ≥ -lam * K := by nlinarith [hlam]
          exact Real.exp_le_exp.mpr this
      _ ≤ ∑ f : Assign N, Real.exp (-lam * (coverLow N f m : ℝ)) :=
          sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun f _ _ => Real.exp_nonneg _)
      _ = _ := sum_exp_neg_coverLow N m lam
  -- `∏ (n-1+e^{-λ}) ≤ |S| · e^{H(e^{-λ}-1)}`
  have h2 : ∏ i : ↥(Icc 1 N), ((i.1 : ℝ) - 1 + Real.exp (-lam))
      ≤ (Fintype.card (Assign N) : ℝ)
        * Real.exp ((∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1)) := by
    have hfac : ∀ i : ↥(Icc 1 N), (i.1 : ℝ) - 1 + Real.exp (-lam)
        ≤ (i.1 : ℝ) * Real.exp ((Real.exp (-lam) - 1) / i.1) := by
      intro i
      have hi : (0:ℝ) < i.1 := by exact_mod_cast (mem_Icc.mp i.2).1
      have hu := Real.add_one_le_exp ((Real.exp (-lam) - 1) / i.1)
      calc (i.1 : ℝ) - 1 + Real.exp (-lam)
          = i.1 * (1 + (Real.exp (-lam) - 1) / i.1) := by field_simp; ring
        _ ≤ i.1 * Real.exp ((Real.exp (-lam) - 1) / i.1) := by
            apply mul_le_mul_of_nonneg_left _ hi.le
            linarith
    have hfac0 : ∀ i : ↥(Icc 1 N), 0 ≤ (i.1 : ℝ) - 1 + Real.exp (-lam) := by
      intro i
      have hi : (1:ℝ) ≤ (i.1 : ℝ) := by exact_mod_cast (mem_Icc.mp i.2).1
      have h2 : (0:ℝ) ≤ Real.exp (-lam) := Real.exp_nonneg _
      linarith
    calc ∏ i : ↥(Icc 1 N), ((i.1 : ℝ) - 1 + Real.exp (-lam))
        ≤ ∏ i : ↥(Icc 1 N), (i.1 * Real.exp ((Real.exp (-lam) - 1) / i.1)) :=
          Finset.prod_le_prod₀ (fun i _ => hfac0 i) (fun i _ => hfac i)
      _ = (∏ i : ↥(Icc 1 N), (i.1 : ℝ)) *
            ∏ i : ↥(Icc 1 N), Real.exp ((Real.exp (-lam) - 1) / i.1) :=
          prod_mul_distrib
      _ = (Fintype.card (Assign N) : ℝ) *
            Real.exp ((∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1)) := by
          congr 1
          · rw [Fintype.card_pi, Nat.cast_prod]
            apply prod_congr rfl; intro i _; rw [Fintype.card_fin]
          · rw [← Real.exp_sum]
            congr 1
            rw [Finset.sum_mul]
            apply sum_congr rfl; intro i _; rw [div_eq_mul_inv, mul_comm]
  -- combine
  have h3 := h1.trans h2
  have h4 : ((univ.filter fun f : Assign N => (coverLow N f m : ℝ) ≤ K).card : ℝ)
      ≤ (Fintype.card (Assign N) : ℝ)
        * Real.exp ((∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1))
        / Real.exp (-lam * K) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr h3
  rw [div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add] at h4
  convert h4 using 3
  ring

/-- **Existence of a good partial assignment.** Some `f` has a small bad set. -/
lemma exists_assign_bad_small (x N : ℕ) (lam K : ℝ) (hlam : 0 ≤ lam) :
    ∃ f : Assign N,
      (((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ K).card : ℝ)
        ≤ x * Real.exp (lam * K +
          (∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1)) := by
  classical
  set E := lam * K + (∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1)
  have hswap : (∑ f : Assign N,
        (((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ K).card : ℝ))
      = ∑ m ∈ Icc 1 x,
        ((univ.filter fun f : Assign N => (coverLow N f m : ℝ) ≤ K).card : ℝ) := by
    simp_rw [← Finset.sum_boole]
    exact Finset.sum_comm
  have htot : (∑ f : Assign N,
        (((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ K).card : ℝ))
      ≤ ∑ f : Assign N, (x : ℝ) * Real.exp E := by
    rw [hswap]
    calc ∑ m ∈ Icc 1 x,
          ((univ.filter fun f : Assign N => (coverLow N f m : ℝ) ≤ K).card : ℝ)
        ≤ ∑ m ∈ Icc 1 x, (Fintype.card (Assign N) : ℝ) * Real.exp E :=
          sum_le_sum fun m _ => card_bad_le N m lam K hlam
      _ = ∑ f : Assign N, (x : ℝ) * Real.exp E := by
          rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
            sum_const, nsmul_eq_mul, Finset.card_univ]
          ring
  have hne : (univ : Finset (Assign N)).Nonempty := univ_nonempty
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hlt : (∑ f : Assign N, (x : ℝ) * Real.exp E)
      < ∑ f : Assign N,
          (((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ K).card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hne fun f _ => hcon f
  linarith [htot]

/-- `e^{λ}(1-λ+λ²/2) ≥ 1` for `λ ≥ 0` (derivative `e^{λ}λ²/2 ≥ 0`). -/
lemma exp_mul_quad_ge_one (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ Real.exp t * (1 - t + t ^ 2 / 2) := by
  have key : ∀ s : ℝ, HasDerivAt (fun u : ℝ => Real.exp u * (1 - u + u ^ 2 / 2))
      (Real.exp s * (s ^ 2 / 2)) s := by
    intro s
    have ha : HasDerivAt (fun u : ℝ => (1:ℝ) - u) (-1) s :=
      (hasDerivAt_id (x := s)).const_sub 1
    have hb : HasDerivAt (fun u : ℝ => u ^ 2 / 2) s s := by
      convert (hasDerivAt_pow 2 s).div_const 2 using 1
      ring
    have hq : HasDerivAt (fun u : ℝ => 1 - u + u ^ 2 / 2) (s - 1) s := by
      convert ha.add hb using 1; ring
    convert (Real.hasDerivAt_exp s).mul hq using 1; ring
  have hmono : MonotoneOn (fun u : ℝ => Real.exp u * (1 - u + u ^ 2 / 2))
      (Set.Icc (0:ℝ) t) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      ((Real.continuous_exp.mul (by fun_prop)).continuousOn)
      (fun s _ => (key s).differentiableAt.differentiableWithinAt)
      (fun s _ => by rw [(key s).deriv]; positivity)
  have h0 : (0:ℝ) ∈ Set.Icc 0 t := Set.left_mem_Icc.mpr ht
  have ht' : t ∈ Set.Icc 0 t := Set.right_mem_Icc.mpr ht
  have h01 := hmono h0 ht' ht
  simp at h01
  linarith

/-- `e^{-λ} ≤ 1 - λ + λ²/2` for `λ ≥ 0`. -/
lemma exp_neg_le_quadratic (lam : ℝ) (hlam : 0 ≤ lam) :
    Real.exp (-lam) ≤ 1 - lam + lam ^ 2 / 2 := by
  have h := exp_mul_quad_ge_one lam hlam
  have hq : (0:ℝ) < 1 - lam + lam ^ 2 / 2 := by nlinarith [sq_nonneg (lam - 1)]
  rw [Real.exp_neg]
  exact (inv_le_iff_one_le_mul₀' (Real.exp_pos lam)).mpr h

/-- The patched assignment: on `n ∈ (N, N+|B|·K]` use the `n`-th patch slot to
cover a designated bad element; on `n ∈ [1,N]` use `f`; elsewhere `0`. -/
def fullAssign (_x N K : ℕ) (B : Finset ℕ) (f : Assign N) (n : ℕ) : ℕ :=
  if h : n ∈ Icc (N + 1) (N + B.card * K) then
    ((B.orderIsoOfFin rfl) ⟨(n - (N + 1)) / K, by
      have h' := mem_Icc.mp h
      have hKpos : 0 < K := by
        rcases Nat.eq_zero_or_pos K with h0 | h0
        · rw [h0, mul_zero, add_zero] at h'; omega
        · exact h0
      exact (Nat.div_lt_iff_lt_mul hKpos).mpr (by omega)⟩ : ↥B).1 % n
  else if h2 : n ∈ Icc 1 N then (f ⟨n, h2⟩ : ℕ)
  else 0

/-- **Patching.** If assignment `f` on `[1,N]` has bad set `B ⊆ [1,x]` with
`|B|·K ≤ x - N`, it extends to a full assignment covering every `m ≤ x` at
least `K` times (using `|B|·K` spare moduli in `(N, x]`). -/
lemma patch (x N K : ℕ) (f : Assign N) (hNx : N ≤ x)
    (B : Finset ℕ)
    (hBK : B.card * K ≤ x - N)
    (hgood : ∀ m ∈ Icc 1 x \ B, K ≤ coverLow N f m) :
    ∃ a : ℕ → ℕ, ∀ m ∈ Icc 1 x, K ≤ coverCount x a m := by
  classical
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · exact ⟨fun _ => 0, fun m _ => Nat.zero_le _⟩
  have hNBK : N + B.card * K ≤ x := by omega
  refine ⟨fullAssign x N K B f, ?_⟩
  intro m hm
  by_cases hmB : m ∈ B
  · -- `m` is bad: it owns the block `{N+1+idx·K+j : j < K}` of `K` moduli.
    set b : ↥B := ⟨m, hmB⟩
    set idx := (B.orderIsoOfFin rfl).symm b with hidx
    have hlt : ∀ j < K, idx.1 * K + j < B.card * K := by
      intro j hj
      have hi := idx.2
      nlinarith [hj, Nat.succ_le_of_lt hi]
    have hpos : ∀ j < K, (N + 1) + (idx.1 * K + j) ∈
        (Icc 1 x).filter (fun n => m ≡ fullAssign x N K B f n [MOD n]) := by
      intro j hj
      have hzone : (N + 1) + (idx.1 * K + j) ∈ Icc (N + 1) (N + B.card * K) := by
        simp only [mem_Icc]; have := hlt j hj; omega
      have hupper : (N + 1) + (idx.1 * K + j) ≤ x := by
        have := hlt j hj; omega
      simp only [mem_filter, mem_Icc]
      refine ⟨⟨by omega, hupper⟩, ?_⟩
      set n := (N + 1) + (idx.1 * K + j)
      have hp : n - (N + 1) = idx.1 * K + j := by simp only [n]; omega
      have hdiv : (n - (N + 1)) / K = idx.1 := by
        rw [hp, Nat.add_comm (idx.1 * K) j, Nat.add_mul_div_right _ _ hK,
          Nat.div_eq_of_lt hj, zero_add]
      have ha : fullAssign x N K B f n = m % n := by
        rw [fullAssign, dite_eq_left hzone]
        have hlt' := hlt j hj
        have hfin : (⟨(n - (N + 1)) / K,
            (Nat.div_lt_iff_lt_mul hK).mpr (by omega)⟩ : Fin B.card) = idx :=
          Fin.ext hdiv
        rw [hfin]
        have hbv : ((B.orderIsoOfFin rfl idx : ↥B) : ℕ) = m := by
          have hb : B.orderIsoOfFin rfl idx = b := by
            rw [hidx]
            exact (B.orderIsoOfFin rfl).apply_symm_apply b
          exact congrArg Subtype.val hb
        rw [hbv]
      rw [ha]
      exact (Nat.mod_modEq m n).symm
    calc K = ((Finset.range K).image (fun j => (N + 1) + (idx.1 * K + j))).card := by
          rw [Finset.card_image_of_injOn (s := Finset.range K)
            (by intro j₁ _ j₂ _ h; dsimp only at h; omega)]
          rw [Finset.card_range]
      _ ≤ coverCount x _ m :=
          card_le_card (Finset.image_subset_iff.mpr
            (fun j hj => hpos j (mem_range.mp hj)))
  · -- `m` is good: already covered `K` times on `[1,N]`.
    have hg := hgood m (Finset.mem_sdiff.mpr ⟨hm, hmB⟩)
    have hsub : (univ.filter fun i : ↥(Icc 1 N) => (f i : ℕ) = m % i.1).card
        ≤ coverCount x (fullAssign x N K B f) m := by
      apply card_le_card_of_injOn (fun i : ↥(Icc 1 N) => i.1)
        (t := (Icc 1 x).filter fun n => m ≡ fullAssign x N K B f n [MOD n])
      · intro i hi
        simp only [Finset.mem_coe] at hi ⊢
        have hi' := (mem_filter.mp hi).2
        simp only [mem_filter, mem_Icc]
        have hiN := mem_Icc.mp i.2
        refine ⟨⟨by omega, by omega⟩, ?_⟩
        have hnz : ¬ i.1 ∈ Icc (N + 1) (N + B.card * K) := by
          simp only [mem_Icc]; omega
        have ha : fullAssign x N K B f i.1 = (f i : ℕ) := by
          rw [fullAssign, dite_eq_right hnz, dite_eq_left i.2]
        rw [ha]
        have hm' : m % i.1 = (f i : ℕ) := hi'.symm
        show m ≡ (f i : ℕ) [MOD i.1]
        rw [← hm']
        exact (Nat.mod_modEq m i.1).symm
      · intro i₁ _ i₂ _ h
        exact Subtype.ext h
    exact hg.trans hsub

/-- **Lower bound.** `F x ≥ H_{x/2} - √(2 H_{x/2} log(4 H_{x/2})) - 1`. -/
lemma F_lower (x : ℕ) :
    ∃ K : ℕ, K ≤ F x ∧ (K : ℝ) ≥ ∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹
      - Real.sqrt (2 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹) *
        Real.log (4 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹))) - 1 := by
  classical
  set N := x / 2 with hN
  set H := ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ with hH
  set T := Real.sqrt (2 * H * Real.log (4 * H)) with hT
  have hHsub : (∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) = H := by
    rw [hH]
    exact Finset.sum_coe_sort (Icc 1 N) (fun n : ℕ => (n : ℝ)⁻¹)
  have hNle : N ≤ x := Nat.div_le_self x 2
  have hHN : H ≤ N := by
    rw [hH]
    calc ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ ≤ ∑ n ∈ Icc 1 N, (1:ℝ) :=
          sum_le_sum fun n hn => inv_le_one_of_one_le₀ (by exact_mod_cast (mem_Icc.mp hn).1)
      _ = N := by simp
  obtain hH0 | hHpos := eq_or_lt_of_le (show (0 : ℝ) ≤ H by positivity)
  · -- `H = 0`: trivial, `K = 0`.
    refine ⟨0, Nat.zero_le _, ?_⟩
    have hT0 : T = 0 := by rw [hT, ← hH0]; simp
    rw [← hH0, hT0]
    norm_num
  · -- `H > 0`: set `λ = T/H`.
    set lam := T / H with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (Real.sqrt_nonneg _) hHpos.le
    set Kreal := H - T with hKr
    set K := ⌊Kreal⌋₊ with hKn
    have hTnn : 0 ≤ T := Real.sqrt_nonneg _
    have hKleH : (K : ℝ) ≤ H := by
      by_cases hz : 0 ≤ Kreal
      · calc (K : ℝ) ≤ Kreal := Nat.floor_le hz
          _ ≤ H := by rw [hKr]; linarith [hTnn]
      · rw [hKn, Nat.floor_eq_zero.mpr (show Kreal < 1 by
            have h := not_le.mp hz; linarith), Nat.cast_zero]
        exact hHpos.le
    have hKge : (K : ℝ) ≥ Kreal - 1 := by
      by_cases hz : 0 ≤ Kreal
      · have h2 := Nat.lt_floor_add_one Kreal
        rw [← hKn] at h2
        linarith
      · rw [hKn, Nat.floor_eq_zero.mpr (show Kreal < 1 by
            have h := not_le.mp hz; linarith), Nat.cast_zero]
        have h := not_le.mp hz
        linarith
    -- the mgf/Chernoff bound at `λ = T/H` gives exponent `≤ -T²/(2H)`
    have hexp : lam * Kreal + (∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1)
        ≤ -T ^ 2 / (2 * H) := by
      rw [hHsub]
      have h2 := exp_neg_le_quadratic lam hlam0
      have key : lam * Kreal + H * (Real.exp (-lam) - 1) ≤ -T ^ 2 / (2 * H) := by
        have h1 : H * (Real.exp (-lam) - 1) ≤ H * (-lam + lam ^ 2 / 2) := by
          apply mul_le_mul_of_nonneg_left _ hHpos.le; linarith
        have h2' : lam * Kreal + H * (-lam + lam ^ 2 / 2) = -T ^ 2 / (2 * H) := by
          have hHne : H ≠ 0 := hHpos.ne'
          rw [hKr, hlam]
          field_simp
          ring
        linarith
      linarith [key]
    -- `exp(-T²/2H) ≤ 1/(4H)` uniformly in `H > 0`
    have htail : Real.exp (-T ^ 2 / (2 * H)) ≤ 1 / (4 * H) := by
      by_cases hlog : 0 ≤ Real.log (4 * H)
      · have hsq : T ^ 2 = 2 * H * Real.log (4 * H) := by
          rw [hT, Real.sq_sqrt (mul_nonneg (by linarith) hlog)]
        have e : -T ^ 2 / (2 * H) = -Real.log (4 * H) := by
          have hHne : H ≠ 0 := hHpos.ne'
          rw [hsq]; field_simp
        rw [e, Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 4 * H)]
        exact le_of_eq (one_div _).symm
      · have hsq : T = 0 := by
          rw [hT]
          exact Real.sqrt_eq_zero'.mpr
            (mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_ge hlog))
        rw [hsq]
        have h4H : 4 * H ≤ 1 := by
          have hle : Real.log (4 * H) ≤ 0 := le_of_not_ge hlog
          calc 4 * H = Real.exp (Real.log (4 * H)) :=
                (Real.exp_log (by linarith)).symm
            _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hle
            _ = 1 := Real.exp_zero
        rw [show (-(0:ℝ) ^ 2) / (2 * H) = 0 by simp, Real.exp_zero,
          le_div_iff₀ (by linarith : (0:ℝ) < 4 * H)]
        nlinarith [h4H]
    obtain ⟨f, hf⟩ := exists_assign_bad_small x N lam Kreal hlam0
    -- `|B|·K ≤ x - N` in naturals, via `|B| ≤ x/(4H)`, `K ≤ H`
    have hB : (((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ Kreal).card : ℝ)
        ≤ x / (4 * H) := by
      calc ((Icc 1 x).filter _).card
          ≤ x * Real.exp (lam * Kreal +
              (∑ i : ↥(Icc 1 N), (i.1 : ℝ)⁻¹) * (Real.exp (-lam) - 1)) := hf
        _ ≤ x * Real.exp (-T ^ 2 / (2 * H)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.exp_le_exp.mpr hexp
        _ ≤ x * (1 / (4 * H)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity); exact htail
        _ = x / (4 * H) := by ring
    have hBK : ((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ Kreal).card * K ≤ x - N := by
      have hreal : ((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ Kreal).card * (K : ℝ)
          ≤ (x : ℝ) - N := by
        calc ((Icc 1 x).filter _).card * K
            ≤ (x / (4 * H)) * H := mul_le_mul hB hKleH (Nat.cast_nonneg _)
              (div_nonneg (Nat.cast_nonneg _) (by linarith))
          _ = x / 4 := by field_simp
          _ ≤ x - N := by
              have hN2 : (N : ℝ) ≤ x / 2 := by
                rw [hN]
                have h2x : (2:ℝ) * ↑(x / 2) ≤ ↑x := by
                  exact_mod_cast (by omega : 2 * (x / 2) ≤ x)
                linarith
              have hx0 : (0:ℝ) ≤ x := Nat.cast_nonneg _
              linarith
      rw [← Nat.cast_mul, ← Nat.cast_sub hNle] at hreal
      exact_mod_cast hreal
    -- good `m`'s are already covered `K` times
    have hgood : ∀ m ∈ Icc 1 x \
        ((Icc 1 x).filter fun m => (coverLow N f m : ℝ) ≤ Kreal),
        K ≤ coverLow N f m := by
      intro m hm
      simp only [Finset.mem_sdiff, Finset.mem_filter] at hm
      have hgt : Kreal < (coverLow N f m : ℝ) := by
        by_contra h
        exact hm.2 ⟨hm.1, not_lt.mp h⟩
      have hle : (K : ℝ) ≤ coverLow N f m := by
        by_cases hz : 0 ≤ Kreal
        · exact (Nat.floor_le hz).trans hgt.le
        · rw [hKn, Nat.floor_eq_zero.mpr (show Kreal < 1 by
              have h := not_le.mp hz; linarith), Nat.cast_zero]
          positivity
      exact_mod_cast hle
    obtain ⟨a, ha⟩ := patch x N K f hNle _ hBK hgood
    refine ⟨K, le_F x K ?_ ⟨a, ha⟩, ?_⟩
    · -- `K ≤ x`
      have : (K : ℝ) ≤ x := by
        calc (K : ℝ) ≤ H := hKleH
          _ ≤ N := hHN
          _ ≤ x := by exact_mod_cast hNle
      exact_mod_cast this
    · -- `K ≥ H - T - 1`
      linarith [hKge]

/-! ## Asymptotic conclusion -/

/-- `log z ≤ 2√z` for `z ≥ 1` (from `log y ≤ y - 1` applied to `√z`). -/
lemma log_le_two_sqrt (z : ℝ) (hz : 1 ≤ z) : Real.log z ≤ 2 * Real.sqrt z := by
  have h1 : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 (by linarith)
  have h := Real.log_le_sub_one_of_pos h1
  have h2 : Real.log z = 2 * Real.log (Real.sqrt z) := by
    rw [Real.log_sqrt (by linarith : (0:ℝ) ≤ z)]; ring
  rw [h2]
  linarith

/-- `log x → ∞` along naturals. -/
lemma tendsto_log_natCast : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- `1/log x → 0`. -/
lemma tendsto_one_div_log :
    Tendsto (fun x : ℕ => (1:ℝ) / Real.log x) atTop (𝓝 0) := by
  simpa only [Function.comp_def, one_div] using
    tendsto_inv_atTop_zero.comp tendsto_log_natCast

/-- `c/log x → 0` for any constant. -/
lemma tendsto_const_div_log (c : ℝ) :
    Tendsto (fun x : ℕ => c / Real.log x) atTop (𝓝 0) := by
  have := tendsto_one_div_log.const_mul c
  simpa [div_eq_mul_inv] using this

/-- `log(x+1)/log x → 1`. -/
lemma tendsto_log_succ_div_log :
    Tendsto (fun x : ℕ => Real.log ((x:ℝ) + 1) / Real.log x) atTop (𝓝 1) := by
  have hupp : Tendsto (fun x : ℕ => (Real.log 2 + Real.log x) / Real.log x)
      atTop (𝓝 1) := by
    have h : Tendsto (fun x : ℕ => Real.log 2 / Real.log x + 1) atTop (𝓝 (0 + 1)) :=
      (tendsto_const_div_log (Real.log 2)).add tendsto_const_nhds
    simp only [zero_add] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : Real.log x ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < x))).ne'
    rw [div_eq_mul_inv, add_div, div_self hpos]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupp
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    rw [le_div_iff₀ hpos]
    have h : Real.log x ≤ Real.log ((x:ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < x)) (by linarith)
    linarith
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hx1 : (x:ℝ) + 1 ≤ 2 * x := by
      have : (1:ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
      linarith
    have h : Real.log ((x:ℝ) + 1) ≤ Real.log (2 * x) :=
      Real.log_le_log (by linarith) hx1
    rw [Real.log_mul (by norm_num) (by positivity)] at h
    exact (div_le_div_iff_of_pos_right hpos).mpr h

/-- `log(x/2 + 1)/log x → 1` (with the `+1` inside `x/2` on naturals). -/
lemma tendsto_log_half_succ_div_log :
    Tendsto (fun x : ℕ => Real.log (((x/2 : ℕ) : ℝ) + 1) / Real.log x) atTop (𝓝 1) := by
  -- squeeze: `log((x+1)/2)/logx ≤ log(x/2+1)/logx ≤ 1`
  have hlow : Tendsto (fun x : ℕ => (Real.log ((x:ℝ) + 1) - Real.log 2) / Real.log x)
      atTop (𝓝 1) := by
    have h := tendsto_log_succ_div_log.sub (tendsto_const_div_log (Real.log 2))
    simp only [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [sub_div]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hge : ((x:ℝ) + 1) / 2 ≤ ((x/2 : ℕ) : ℝ) + 1 := by
      have h' : (x:ℝ) - 1 ≤ 2 * ((x/2 : ℕ) : ℝ) := by
        have h'' : x - 1 ≤ 2 * (x/2) := by omega
        have h2 : ((x - 1 : ℕ) : ℝ) ≤ (2 * (x/2) : ℕ) := by exact_mod_cast h''
        rw [Nat.cast_sub (by omega : 1 ≤ x), Nat.cast_mul, Nat.cast_two, Nat.cast_one] at h2
        linarith
      linarith
    have h : Real.log ((x:ℝ) + 1) - Real.log 2 ≤ Real.log (((x/2 : ℕ) : ℝ) + 1) := by
      rw [← Real.log_div (by positivity : (0:ℝ) < (x:ℝ) + 1).ne' (by norm_num)]
      exact Real.log_le_log (by positivity) hge
    exact (div_le_div_iff_of_pos_right hpos).mpr h
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hle : ((x/2 : ℕ) : ℝ) + 1 ≤ x := by
      have h' : (x/2 : ℕ) + 1 ≤ x := by omega
      have h2 : (((x/2 : ℕ) + 1 : ℕ) : ℝ) ≤ (x:ℝ) := by exact_mod_cast h'
      push_cast at h2
      linarith
    have h : Real.log (((x/2 : ℕ) : ℝ) + 1) ≤ Real.log x :=
      Real.log_le_log (by positivity) hle
    calc Real.log (((x/2 : ℕ) : ℝ) + 1) / Real.log x
        ≤ Real.log x / Real.log x := (div_le_div_iff_of_pos_right hpos).mpr h
      _ = 1 := div_self hpos.ne'

/-- `(1 + log x)/log x → 1`. -/
lemma tendsto_one_add_log_div_log :
    Tendsto (fun x : ℕ => (1 + Real.log (x:ℝ)) / Real.log x) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℕ => (1:ℝ) / Real.log (x:ℝ) + 1) atTop (𝓝 (0 + 1)) :=
    tendsto_one_div_log.add tendsto_const_nhds
  simp only [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hpos : Real.log x ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < x))).ne'
  rw [add_div, div_self hpos]

/-- `H_{x/2}/log x → 1`. -/
lemma tendsto_harmonic_half_div_log :
    Tendsto (fun x : ℕ =>
      (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹) / Real.log x) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_log_half_succ_div_log tendsto_one_add_log_div_log
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have h := log_le_harmonic (x/2)
    exact (div_le_div_iff_of_pos_right hpos).mpr h
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have h := harmonic_le (x/2) (by omega : 1 ≤ x/2)
    have hle : Real.log ((x/2 : ℕ) : ℝ) ≤ Real.log (x:ℝ) :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega))
        (by exact_mod_cast Nat.div_le_self x 2)
    exact (div_le_div_iff_of_pos_right hpos).mpr (by linarith)

/-- `H_x/log x → 1`. -/
lemma tendsto_harmonic_div_log :
    Tendsto (fun x : ℕ =>
      (∑ n ∈ Icc 1 x, (n : ℝ)⁻¹) / Real.log x) atTop (𝓝 1) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_log_succ_div_log tendsto_one_add_log_div_log
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have h := log_le_harmonic x
    exact (div_le_div_iff_of_pos_right hpos).mpr h
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have h := harmonic_le x (by omega : 1 ≤ x)
    exact (div_le_div_iff_of_pos_right hpos).mpr h

/-- The error term `T_x / log x → 0`. -/
lemma tendsto_T_div_log :
    Tendsto (fun x : ℕ =>
      Real.sqrt (2 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹) *
        Real.log (4 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹))) / Real.log x)
      atTop (𝓝 0) := by
  set H := fun x : ℕ => ∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹ with hH
  set u := fun x : ℕ => Real.log (x : ℝ) with hu
  -- upper envelope `√(16√2·√u/u) → 0`
  have hsqrt : Tendsto (fun x : ℕ => Real.sqrt (Real.sqrt (u x))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_log_natCast)
  have hCup : Tendsto (fun x : ℕ => Real.sqrt (16 * Real.sqrt 2) / Real.sqrt (Real.sqrt (u x)))
      atTop (𝓝 (Real.sqrt (16 * Real.sqrt 2) * 0)) :=
    (tendsto_inv_atTop_zero.comp hsqrt).const_mul (Real.sqrt (16 * Real.sqrt 2))
  rw [mul_zero] at hCup
  have hC : Tendsto (fun x : ℕ =>
      Real.sqrt (16 * Real.sqrt 2 * Real.sqrt (u x) / u x)) atTop (𝓝 0) := by
    refine hCup.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hu0 : (0:ℝ) < u x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    have hu0' : u x ≠ 0 := hu0.ne'
    have e : Real.sqrt (16 * Real.sqrt 2 * Real.sqrt (u x) / u x)
        = Real.sqrt ((16 * Real.sqrt 2) / Real.sqrt (u x)) := by
      congr 1
      rw [div_eq_div_iff hu0' ((Real.sqrt_pos.mpr hu0).ne'), mul_assoc,
        Real.mul_self_sqrt hu0.le]
    rw [e, Real.sqrt_div (by positivity : (0:ℝ) ≤ 16 * Real.sqrt 2),
      div_eq_mul_inv]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hu0 : (0:ℝ) < u x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    exact div_nonneg (Real.sqrt_nonneg _) hu0.le
  · filter_upwards [eventually_ge_atTop 4] with x hx
    have hu1 : (1:ℝ) ≤ u x := by
      have h4 : Real.log 4 ≤ Real.log (x:ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hx)
      have h42 : (1:ℝ) ≤ Real.log 4 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        linarith [Real.exp_one_lt_d9]
      linarith
    have hN2 : 2 ≤ x / 2 := by omega
    have hHge : (3:ℝ)/2 ≤ H x := by
      have hsub : Finset.Icc (1:ℕ) 2 ⊆ Finset.Icc 1 (x/2) := by
        intro n hn; simp only [Finset.mem_Icc] at hn ⊢; omega
      have e : ∑ n ∈ Finset.Icc (1:ℕ) 2, (n:ℝ)⁻¹ = (3:ℝ)/2 := by
        have hs : Finset.Icc (1:ℕ) 2 = {1, 2} := by
          ext m; simp [Finset.mem_Icc]; omega
        rw [hs]
        norm_num
      have hle : ∑ n ∈ Finset.Icc (1:ℕ) 2, (n : ℝ)⁻¹ ≤ H x := by
        apply sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        positivity
      rw [e] at hle
      exact hle
    have hHle : H x ≤ 1 + u x := by
      have hxr : (4:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
      have hh := harmonic_le (x/2) (by omega : 1 ≤ x/2)
      have h1 : Real.log ((x/2 : ℕ) : ℝ) ≤ Real.log ((x:ℝ)/2) := by
        apply Real.log_le_log (Nat.cast_pos.mpr (by omega))
        have h2x : (2:ℝ) * ↑(x / 2) ≤ ↑x := by
          exact_mod_cast (by omega : 2 * (x / 2) ≤ x)
        linarith
      have h2 : Real.log ((x:ℝ)/2) ≤ u x :=
        Real.log_le_log (by linarith : (0:ℝ) < (x:ℝ)/2)
          (by linarith : (x:ℝ)/2 ≤ x)
      linarith
    have hlog4H : Real.log (4 * H x) ≤ 4 * Real.sqrt (H x) := by
      have h1 := log_le_two_sqrt (4 * H x) (by linarith : (1:ℝ) ≤ 4 * H x)
      have h2 : Real.sqrt (4 * H x) = 2 * Real.sqrt (H x) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        congr 1
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h2] at h1; linarith
    have hTnn : (0:ℝ) ≤ 2 * H x * Real.log (4 * H x) :=
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 * H x)
        (Real.log_nonneg (by linarith : (1:ℝ) ≤ 4 * H x))
    have hT2 : 2 * H x * Real.log (4 * H x)
        ≤ 16 * Real.sqrt 2 * u x * Real.sqrt (u x) := by
      calc 2 * H x * Real.log (4 * H x)
          ≤ 2 * H x * (4 * Real.sqrt (H x)) :=
            mul_le_mul_of_nonneg_left hlog4H (by linarith : (0:ℝ) ≤ 2 * H x)
        _ = 8 * (H x * Real.sqrt (H x)) := by ring
        _ ≤ 8 * ((1 + u x) * Real.sqrt (1 + u x)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
            exact mul_le_mul hHle (Real.sqrt_le_sqrt hHle)
              (Real.sqrt_nonneg _) (by linarith)
        _ ≤ 8 * ((2 * u x) * Real.sqrt (2 * u x)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
            exact mul_le_mul (by linarith : (1:ℝ) + u x ≤ 2 * u x)
              (Real.sqrt_le_sqrt (by linarith))
              (Real.sqrt_nonneg _) (by linarith)
        _ = 16 * Real.sqrt 2 * u x * Real.sqrt (u x) := by
            rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]; ring
    have hTpos : (0:ℝ) ≤ Real.sqrt (2 * H x * Real.log (4 * H x)) / u x := by
      exact div_nonneg (Real.sqrt_nonneg _) (by linarith)
    have hu0' : u x ≠ 0 := ne_of_gt (by linarith)
    calc Real.sqrt (2 * H x * Real.log (4 * H x)) / u x
        = Real.sqrt ((Real.sqrt (2 * H x * Real.log (4 * H x)) / u x) ^ 2) :=
          (Real.sqrt_sq hTpos).symm
      _ ≤ Real.sqrt (16 * Real.sqrt 2 * Real.sqrt (u x) / u x) := by
          apply Real.sqrt_le_sqrt
          rw [div_pow, Real.sq_sqrt hTnn, div_le_iff₀ (pow_pos (by linarith) 2)]
          have e : 16 * Real.sqrt 2 * Real.sqrt (u x) / u x * u x ^ 2
              = 16 * Real.sqrt 2 * u x * Real.sqrt (u x) := by
            field_simp
          rw [e]
          exact hT2

/-- **Main theorem** (Erdős 1980; JSP-001010 / Erdős Problem #1205):
`F x ∼ log x`. -/
theorem jsp_001010 :
    Tendsto (fun x : ℕ => (F x : ℝ) / Real.log x) atTop (𝓝 1) := by
  have hlower : Tendsto (fun x : ℕ =>
      ((∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹)
        - Real.sqrt (2 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹) *
          Real.log (4 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹))) - 1) / Real.log x)
      atTop (𝓝 1) := by
    have h := (tendsto_harmonic_half_div_log.sub tendsto_T_div_log).sub
      tendsto_one_div_log
    simp only [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : Real.log x ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (by omega : 1 < x))).ne'
    field_simp
  have hupper : Tendsto (fun x : ℕ =>
      ((∑ n ∈ Icc 1 x, (n : ℝ)⁻¹) + 1) / Real.log x) atTop (𝓝 1) := by
    have h := tendsto_harmonic_div_log.add tendsto_one_div_log
    simp only [add_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [add_div]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    obtain ⟨K, hKle, hKge⟩ := F_lower x
    have h1 : (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹)
        - Real.sqrt (2 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹) *
          Real.log (4 * (∑ n ∈ Icc 1 (x/2), (n : ℝ)⁻¹))) - 1 ≤ (F x : ℝ) :=
      le_trans hKge (by exact_mod_cast hKle)
    exact (div_le_div_iff_of_pos_right hpos).mpr h1
  · filter_upwards [eventually_ge_atTop 2] with x hx
    have hpos : (0:ℝ) < Real.log x := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
    exact (div_le_div_iff_of_pos_right hpos).mpr (F_upper x (by omega))
