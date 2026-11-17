/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.ConnectedMap
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
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

/-! ### The part of a fibration over a subspace -/

namespace ContinuousMap

variable {E' B' : Type u} [TopologicalSpace E'] [TopologicalSpace B'] {Y : Set B'} {y : B'}

/-- The inclusion `p⁻¹(y) → p⁻¹(Y)` of the fibre over a point `y ∈ Y` into the preimage of `Y`. -/
def preimageInclusion (p : C(E', B')) (hy : y ∈ Y) :
    TopCat.of (p ⁻¹' {y}) ⟶ TopCat.of (p ⁻¹' Y) :=
  TopCat.ofHom (ContinuousMap.inclusion (Set.preimage_mono (Set.singleton_subset_iff.2 hy)))

@[simp]
theorem hom_preimageInclusion (p : C(E', B')) (hy : y ∈ Y) :
    (p.preimageInclusion hy).hom =
      ContinuousMap.inclusion (Set.preimage_mono (Set.singleton_subset_iff.2 hy)) :=
  (rfl)

theorem coe_preimageInclusion_apply (p : C(E', B')) (hy : y ∈ Y) (x : p ⁻¹' {y}) :
    ((p.preimageInclusion hy).hom x : E') = x :=
  (rfl)

/-- The fibre `p⁻¹(y)` is the fibre over `y` of the restriction `p⁻¹(Y) → Y`. -/
def preimageSingletonHomeomorphFiber (p : C(E', B')) (hy : y ∈ Y) :
    (p ⁻¹' {y}) ≃ₜ (p.restrictPreimage Y ⁻¹' {⟨y, hy⟩}) where
  toFun e := ⟨⟨e.1, Set.mem_preimage.2 ((Set.mem_singleton_iff.1 e.2).symm ▸ hy)⟩,
    Subtype.ext e.2⟩
  invFun e := ⟨e.1.1, congrArg Subtype.val e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem coe_coe_preimageSingletonHomeomorphFiber_apply (p : C(E', B')) (hy : y ∈ Y)
    (e : p ⁻¹' {y}) : ((p.preimageSingletonHomeomorphFiber hy e).1 : E') = e :=
  (rfl)

@[simp]
theorem coe_preimageSingletonHomeomorphFiber_symm_apply (p : C(E', B')) (hy : y ∈ Y)
    (e : p.restrictPreimage Y ⁻¹' {⟨y, hy⟩}) :
    ((p.preimageSingletonHomeomorphFiber hy).symm e : E') = e.1.1 :=
  (rfl)

/-- The inclusion `p⁻¹(y) → p⁻¹(Y)` is the fibre inclusion of the restriction `p⁻¹(Y) → Y`, up to
`ContinuousMap.preimageSingletonHomeomorphFiber`. -/
theorem preimageInclusion_eq (p : C(E', B')) (hy : y ∈ Y) :
    p.preimageInclusion hy =
      (TopCat.isoOfHomeo (p.preimageSingletonHomeomorphFiber hy)).hom ≫
        (TopCat.ofHom (p.restrictPreimage Y)).fiberι ⟨y, hy⟩ :=
  TopCat.ext fun x ↦ by
    rw [ConcreteCategory.comp_apply, TopCat.Hom.fiberι_apply]
    exact Subtype.ext (p.coe_coe_preimageSingletonHomeomorphFiber_apply hy x).symm

end ContinuousMap

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
        q.preimageInclusion hy :=
  _root_.TopCat.ext fun x ↦ Subtype.ext <| by simp [toHomotopyEquiv_apply]

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
