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
* `TauCeti.TopCat.fiberSingularHomologyIsoOfPath`: a path in `B` induces singular homology
  isomorphisms between the fibres over its endpoints in every degree.

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

section ConnectedBase

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

end ConnectedBase

/-- **Path transport on singular homology of fibres of a Serre fibration.** A path `γ` from `b₀` to
`b₁` in `B` induces an isomorphism `H_n(p⁻¹(b₀); R) ≅ H_n(p⁻¹(b₁); R)` in every degree `n` over any
ring `R`, obtained by pulling `p` back to the contractible interval `ULift unitInterval` and
inverting the homology maps of the endpoint fibre inclusions. -/
noncomputable def fiberSingularHomologyIsoOfPath {E B : _root_.TopCat.{u}} {p : E ⟶ B}
    (hp : serreFibrations p) (R : Type u) [Ring R] {b₀ b₁ : B} (γ : Path b₀ b₁) (n : ℕ) :
    (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj (p.fiber b₀)) ≅
      (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).obj (p.fiber b₁)) :=
  let g : _root_.TopCat.of (ULift.{u} unitInterval) ⟶ B :=
    _root_.TopCat.ofHom ⟨fun t ↦ γ t.down, γ.continuous.comp continuous_uliftDown⟩
  let p' := _root_.TopCat.pullbackFst g p
  have hp' : serreFibrations p' := mem_serreFibrations_pullbackFst hp g
  have : ContractibleSpace (_root_.TopCat.of (ULift.{u} unitInterval)) :=
    have : ContractibleSpace unitInterval :=
      (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, unitInterval.zero_mem⟩
    Homeomorph.ulift.contractibleSpace
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (p'.fiberι (ULift.up (0 : unitInterval)))) :=
    isIso_singularHomologyMap_fiberι R hp' (n := n + 1) (fun _ _ ↦ inferInstance)
      (Nat.lt_succ_self n)
  have : IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (p'.fiberι (ULift.up (1 : unitInterval)))) :=
    isIso_singularHomologyMap_fiberι R hp' (n := n + 1) (fun _ _ ↦ inferInstance)
      (Nat.lt_succ_self n)
  ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).mapIso
      (eqToIso (congrArg p.fiber γ.source.symm) ≪≫
        (p.fiberPullbackFstIso g (ULift.up (0 : unitInterval))).symm) ≪≫
    asIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (p'.fiberι (ULift.up (0 : unitInterval)))) ≪≫
    (asIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).map
      (p'.fiberι (ULift.up (1 : unitInterval))))).symm ≪≫
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)).mapIso
      (p.fiberPullbackFstIso g (ULift.up (1 : unitInterval)) ≪≫
        eqToIso (congrArg p.fiber γ.target))

end TauCeti.TopCat
