# JSP-001010: covering multiplicity F(x) ~ log x — Lean formalization

Lean 4 + Mathlib formalization of the answer to JSP-001010
(Erdős Problem #1205, solved by Erdős in 1980):

> Let `F(x)` be the largest `k` such that there is an assignment
> `a : ℕ → ℕ` with every `m ∈ [1,x]` satisfying `m ≡ aₙ (mod n)` for at
> least `k` values of `n ∈ [1,x]`. Then `F(x) ∼ log x`.

The main theorem is

```lean
theorem jsp_001010 :
    Tendsto (fun x : ℕ => (F x : ℝ) / Real.log x) atTop (𝓝 1)
```

with `F` defined concretely as `Nat.findGreatest` of a decidable
covering property, so no choice principles beyond the standard three
axioms are used.

## Proof idea

Upper bound (`F_upper`): double counting. For a fixed assignment `a`,
`∑_{m≤x} cover(m) = ∑_{n≤x} #{m ≤ x : m ≡ aₙ (mod n)} ≤ x·(1 + H_x)`
since each residue class mod `n` has at most `⌊x/n⌋ + 1` elements. If
every `m` is covered `≥ k` times then `x·k ≤ x·(1+H_x)`, so
`F(x) ≤ 1 + H_x`.

Lower bound (`F_lower`): take `N = ⌊x/2⌋` and count all assignments on
`[1,N]` (each `n` gets a residue `aₙ ∈ Fin n`). For each `m`, the
coverage `X_m = #{n ≤ N : aₙ ≡ m}` has moment generating bound

```
∑_f exp(-λ X_m) = ∏_{n≤N} (n - 1 + e^{-λ}) ≤ |Assign|·exp(H_N(e^{-λ}-1))
```

hence a Chernoff tail estimate `#{f : X_m ≤ K} ≤ |Assign|·exp(λK +
H_N(e^{-λ}-1))`. Choosing `λ = T/H` with
`T = √(2 H_N log(4 H_N))` makes the total number of pairs `(f, m)` with
`X_m ≤ K` smaller than `|Assign|`, so some `f` has bad set `B` with
`|B| ≤ x/(4H)`. Since `|B|·K ≤ x - N`, each bad `m` can be repaired by a
block of `K` spare moduli in `(N, N + |B|K]` (`patch`), giving
`F(x) ≥ ⌊H_{x/2} - T - 1⌋`.

Finally `H_{x/2}/log x → 1` and `T/log x → 0`, so squeezing gives
`F(x)/log x → 1` (`jsp_001010`).

## Verification

- `lake build` compiles `Jsp001010.lean` with no errors and no warnings.
- `#print axioms jsp_001010` reports only `propext`,
  `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, or `native_decide` anywhere in the file.

Toolchain: Lean `v4.34.0`, Mathlib pinned via `lake-manifest.json`.
