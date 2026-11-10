/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

/-!
# Homology of the fibre inclusion over a highly connected base

Let `p : E → B` be a Serre fibration and `b : B` a point at which `π_k(B, b)` is trivial for every
`k ≤ n`, so that `B` is path-connected and `n`-connected. The inclusion of the fibre
`F = p⁻¹(b) → E` is then an `n`-connected map
(`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`), so it induces isomorphisms
`H_m(F; R) → H_m(E; R)` for `m < n` and surjections for `m = n`, with coefficients in any ring
`R`.

This is the comparison between the homology of a fibre and of the total space that is usually read
off the Serre spectral sequence, whose `E²` page vanishes in the columns `1 ≤ p ≤ n`; here it
follows from the exact homotopy sequence and the homology comparison for `n`-connected maps.
Barraud, Damian, Humilière and Oancea apply it to the evaluation fibration
`P_{Q→Y} 𝓛₀ Q → Y` with fibre `Ω²Q` over a highly connected submanifold `Y` (Lemma 7.7), and to
double loop spaces of sphere bundles over highly connected bases (Proposition 6.23).

## Main results

* `TauCeti.TopCat.isIso_singularHomologyMap_fiberι`: the fibre inclusion is an isomorphism on
  `H_m` for `m < n`.
* `TauCeti.TopCat.epi_singularHomologyMap_fiberι`: the fibre inclusion is surjective on `H_n`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Proposition 4.21.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23 and Lemma 7.7.
-/

public section

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B} {b : B} {n : ℕ} (R : Type u) [Ring R]

/-- **The fibre inclusion over an `n`-connected base is a homology isomorphism below degree `n`.**
For a Serre fibration `p : E → B` and a point `b` with `π_k(B, b)` trivial for every `k ≤ n`, the
inclusion of the fibre `p⁻¹(b) → E` induces isomorphisms `H_m(p⁻¹(b); R) → H_m(E; R)` for every
`m < n`. -/
theorem isIso_singularHomologyMap_fiberι (hp : serreFibrations p)
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (p.fiberι b)) :=
  (isNConnected_fiberι_of_mem_serreFibrations hp hB).isIso_singularHomologyMap R hm

/-- **The fibre inclusion over an `n`-connected base is surjective on homology in degree `n`.**
For a Serre fibration `p : E → B` and a point `b` with `π_k(B, b)` trivial for every `k ≤ n`, the
inclusion of the fibre `p⁻¹(b) → E` induces surjections `H_m(p⁻¹(b); R) → H_m(E; R)` for every
`m ≤ n`. -/
theorem epi_singularHomologyMap_fiberι (hp : serreFibrations p)
    (hB : ∀ k ≤ n, Subsingleton (π_ k B b)) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (p.fiberι b)) :=
  (isNConnected_fiberι_of_mem_serreFibrations hp hB).epi_singularHomologyMap R hm

end TauCeti.TopCat
