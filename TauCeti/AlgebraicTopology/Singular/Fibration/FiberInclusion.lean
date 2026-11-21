/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.Homotopy.SerreFibration.Connected

import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence

/-!
# Homology of the fibre inclusion over a highly connected base

Let `p : E → B` be a Serre fibration and `b : B` a point at which `π_k(B, b)` is trivial for every
`k ≤ n`, so that `B` is path-connected and `n`-connected. The inclusion of the fibre
`F = p⁻¹(b) → E` is then an `n`-connected map
(`TauCeti.TopCat.isNConnected_fiberι_of_mem_serreFibrations`), so it induces isomorphisms
`H_m(F; R) → H_m(E; R)` for `m < n` and surjections for `m = n`, with coefficients in any ring
`R`. Over a contractible base `B`, every fibre inclusion is a weak homotopy equivalence
(`TauCeti.TopCat.isWeakHomotopyEquivalence_fiberι_of_contractibleSpace`) and therefore induces
isomorphisms `H_n(F; M) → H_n(E; M)` in every degree for any coefficient module `M`
(`TauCeti.TopCat.isIso_singularHomologyMap_fiberι_of_contractibleSpace`).

This is the comparison between the homology of a fibre and of the total space that is usually read
off the Serre spectral sequence, whose `E²` page vanishes in the columns `1 ≤ p ≤ n`; here it
follows from the exact homotopy sequence and the homology comparison for `n`-connected maps.
Barraud, Damian, Humilière and Oancea apply it to the evaluation fibration
`P_{Q→Y} 𝓛₀ Q → Y` with fibre `Ω²Q` over a highly connected submanifold `Y` (Lemma 7.7), and to
double loop spaces of sphere bundles over highly connected bases (Proposition 6.23).

The comparison is often applied to a fibration restricted to the preimage `p⁻¹(Y)` of a subspace
`Y` of the base, for instance the maps of a sphere sending a base point into `Y`. In this form,
for a Serre fibration `p : E → B` and a point `y` of a subspace `Y ⊆ B` at which `Y` is
`n`-connected, the inclusion `p⁻¹(y) → p⁻¹(Y)` is an isomorphism on `H_m` for `m < n` and onto on
`H_n` (`TauCeti.TopCat.isIso_singularHomologyMap_preimageInclusion`,
`TauCeti.TopCat.epi_singularHomologyMap_preimageInclusion`). Only the restriction `p⁻¹(Y) → Y`
needs to be a Serre fibration. Both properties are invariant under fibre homotopy equivalence
(`TauCeti.FiberHomotopyEquiv.isIso_singularHomologyMap_preimageInclusion_iff`,
`TauCeti.FiberHomotopyEquiv.epi_singularHomologyMap_preimageInclusion_iff`), so they also hold
for maps that are merely fibre homotopy equivalent to a Serre fibration, such as the endpoint map
of a space of Moore paths.

## Main results

* `TauCeti.TopCat.isIso_singularHomologyMap_fiberι`: the fibre inclusion is an isomorphism on
  `H_m` for `m < n`.
* `TauCeti.TopCat.epi_singularHomologyMap_fiberι`: the fibre inclusion is surjective on `H_n`.
* `TauCeti.TopCat.isIso_singularHomologyMap_fiberι_of_contractibleSpace`: over a contractible
  base, the fibre inclusion is an isomorphism on `H_n(-; M)` in every degree and for any
  coefficient module `M`.
* `TauCeti.TopCat.isIso_singularHomologyMap_preimageInclusion`,
  `TauCeti.TopCat.epi_singularHomologyMap_preimageInclusion`: the same for the inclusion
  `p⁻¹(y) → p⁻¹(Y)` over an `n`-connected subspace `Y`.
* `TauCeti.FiberHomotopyEquiv.isIso_singularHomologyMap_preimageInclusion_iff`,
  `TauCeti.FiberHomotopyEquiv.epi_singularHomologyMap_preimageInclusion_iff`: these properties of
  `p⁻¹(y) → p⁻¹(Y)` are invariant under fibre homotopy equivalence.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 and Proposition 4.21.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.23 and Lemma 7.7.
-/

public section

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy

universe u v

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

/-- **Over a contractible base, every fibre inclusion of a Serre fibration induces an isomorphism
on singular homology** in every degree `n` and with coefficients in any module `M`. -/
theorem isIso_singularHomologyMap_fiberι_of_contractibleSpace {E B : _root_.TopCat.{u}}
    {p : E ⟶ B} (hp : serreFibrations p) [ContractibleSpace B] {R : Type v} [Ring R]
    (M : ModuleCat.{u} R) (b : B) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (p.fiberι b)) :=
  (isWeakHomotopyEquivalence_fiberι_of_contractibleSpace hp b).isIso_singularHomologyMap M n

end TauCeti.TopCat

namespace TauCeti.TopCat

section Preimage

variable {n : ℕ} (R : Type u) [Ring R] {E' B' : Type u} [TopologicalSpace E'] [TopologicalSpace B']
  {Y : Set B'} {y : B'}

/-- **The fibre in the part over a highly connected subspace.** Let `p : E → B` be a map whose
restriction `p⁻¹(Y) → Y` to a subspace `Y` is a Serre fibration, and let `y ∈ Y` be a point at which
`π_k(Y, y)` is trivial for every `k ≤ n`. Then the inclusion `p⁻¹(y) → p⁻¹(Y)` induces isomorphisms
`H_m(p⁻¹(y); R) → H_m(p⁻¹(Y); R)` for every `m < n`. -/
theorem isIso_singularHomologyMap_preimageInclusion {p : C(E', B')}
    (hp : serreFibrations (_root_.TopCat.ofHom (p.restrictPreimage Y))) (hy : y ∈ Y)
    (hY : ∀ k ≤ n, Subsingleton (π_ k Y ⟨y, hy⟩)) {m : ℕ} (hm : m < n) :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (p.preimageInclusion hy)) := by
  have := isIso_singularHomologyMap_fiberι R hp hY hm
  rw [ContinuousMap.preimageInclusion_eq, Functor.map_comp]
  infer_instance

/-- **The fibre in the part over a highly connected subspace, in the top degree.** Let `p : E → B`
be a map whose restriction `p⁻¹(Y) → Y` to a subspace `Y` is a Serre fibration, and let `y ∈ Y` be a
point at which `π_k(Y, y)` is trivial for every `k ≤ n`. Then the inclusion `p⁻¹(y) → p⁻¹(Y)`
induces surjections `H_m(p⁻¹(y); R) → H_m(p⁻¹(Y); R)` for every `m ≤ n`. -/
theorem epi_singularHomologyMap_preimageInclusion {p : C(E', B')}
    (hp : serreFibrations (_root_.TopCat.ofHom (p.restrictPreimage Y))) (hy : y ∈ Y)
    (hY : ∀ k ≤ n, Subsingleton (π_ k Y ⟨y, hy⟩)) {m : ℕ} (hm : m ≤ n) :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
      (p.preimageInclusion hy)) := by
  have := epi_singularHomologyMap_fiberι R hp hY hm
  rw [ContinuousMap.preimageInclusion_eq, Functor.map_comp]
  infer_instance

end Preimage

end TauCeti.TopCat

namespace TauCeti.FiberHomotopyEquiv

open TauCeti.TopCat

variable (R : Type u) [Ring R] {E E' B : Type u} [TopologicalSpace E] [TopologicalSpace E']
  [TopologicalSpace B] {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) {Y : Set B}
  {y : B} (hy : y ∈ Y) (m : ℕ)
include Φ

/-- A fibre homotopy equivalence carries the inclusion `p⁻¹(y) → p⁻¹(Y)` to the inclusion
`q⁻¹(y) → q⁻¹(Y)`. -/
private theorem preimageInclusion_comp :
    p.preimageInclusion hy ≫ _root_.TopCat.ofHom (Φ.restrictPreimage Y).toHomotopyEquiv.toFun =
      _root_.TopCat.ofHom (Φ.restrictPreimage {y}).toHomotopyEquiv.toFun ≫
        q.preimageInclusion hy := by
  have h (S : Set B) :
      (Φ.restrictPreimage S).toHomotopyEquiv.toFun = (Φ.restrictPreimage S).toFun :=
    ContinuousMap.ext (toHomotopyEquiv_apply _)
  rw [h, h, restrictPreimage_toFun, restrictPreimage_toFun]
  exact ContinuousMap.preimageInclusion_comp_ofHom_restrictPreimageMap Φ.comp_toFun hy

/-- On homology, the commutative square of `preimageInclusion_comp`. Its horizontal maps, induced
by the restrictions of `Φ`, are isomorphisms. -/
private theorem singularHomologyMap_preimageInclusion_comp :
    ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (p.preimageInclusion hy) ≫
      ((Φ.restrictPreimage Y).toHomotopyEquiv.singularHomologyIso (ModuleCat.of R R) m).hom =
    ((Φ.restrictPreimage {y}).toHomotopyEquiv.singularHomologyIso (ModuleCat.of R R) m).hom ≫
      ((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (q.preimageInclusion hy) := by
  simp only [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, ← Functor.map_comp]
  exact congrArg _ (preimageInclusion_comp Φ hy)

/-- **Fibre homotopy invariance of the fibre comparison.** For a fibre homotopy equivalence between
`p` and `q` over `B`, the inclusion `p⁻¹(y) → p⁻¹(Y)` is an isomorphism on `H_m` exactly when
`q⁻¹(y) → q⁻¹(Y)` is. -/
theorem isIso_singularHomologyMap_preimageInclusion_iff :
    IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (p.preimageInclusion hy)) ↔
      IsIso (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (q.preimageInclusion hy)) := by
  rw [← isIso_comp_right_iff _
      ((Φ.restrictPreimage Y).toHomotopyEquiv.singularHomologyIso (ModuleCat.of R R) m).hom,
    singularHomologyMap_preimageInclusion_comp, isIso_comp_left_iff]

/-- **Fibre homotopy invariance of the fibre comparison, for surjectivity.** For a fibre homotopy
equivalence between `p` and `q` over `B`, the inclusion `p⁻¹(y) → p⁻¹(Y)` is onto on `H_m` exactly
when `q⁻¹(y) → q⁻¹(Y)` is. -/
theorem epi_singularHomologyMap_preimageInclusion_iff :
    Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (p.preimageInclusion hy)) ↔
      Epi (((singularHomologyFunctor (ModuleCat.{u} R) m).obj (ModuleCat.of R R)).map
        (q.preimageInclusion hy)) := by
  rw [← epi_comp_iff_of_isIso _
      ((Φ.restrictPreimage Y).toHomotopyEquiv.singularHomologyIso (ModuleCat.of R R) m).hom,
    singularHomologyMap_preimageInclusion_comp, epi_comp_iff_of_epi]

end TauCeti.FiberHomotopyEquiv
