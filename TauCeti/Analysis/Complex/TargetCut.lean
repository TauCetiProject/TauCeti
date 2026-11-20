/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Data.Finite.Perm
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.DiscreteSubset
import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv

/-!
# Stabilizing sphere components by a transverse target cut

A component of a genus-zero curve with fewer than three special points is not a stable pointed
curve: the Möbius transformations fixing its special points form a positive-dimensional group. In
the virtual constructions of moduli spaces of pseudoholomorphic curves (Pardon) such a component is
stabilized by a *target cut*: a real codimension-two submanifold `D` of the target which the map
`u` of the component meets transversally. The *full* preimage `u⁻¹(D)` is then a finite set, and
it is added to the domain as an *unordered* set of further marked points. This file proves the
facts that make this stabilization work, for a sphere with a special point at `∞`.

Write the sphere as `K ∪ {∞}` for a field `K` (for curves, `K = ℂ`). The Möbius transformations
fixing `∞` are the affine automorphisms `z ↦ a z + b` of `K`, the group `K ≃ᵃ[K] K`. A component
with special points `∞` and `P ⊆ K`, for instance `P = ∅` or `P = {0}`, is a map `u : K → X`.

* **Stability of the stabilized domain.** The automorphisms of the sphere fixing `∞` and every
  point of `P`, and mapping a finite set `C` onto itself, form the subgroup
  `TauCeti.markingStabilizer P C`. Each of them permutes `C` (`TauCeti.markingPerm`), and when
  `P ∪ C` contains two distinct points this permutation determines it
  (`TauCeti.markingPerm_injective`), because an affine automorphism fixing two distinct points is
  the identity (`AffineEquiv.eq_one_of_apply_eq_self_of_apply_eq_self`). So the sphere with the
  special point `∞`, the marked points `P` and the unordered marking `C` has finitely many
  automorphisms, whose number divides `|C|!`
  (`TauCeti.card_markingStabilizer_dvd_factorial`). With an ordering of `C` it has none but the
  identity.
* **Forgetting the cut points does not change the isotropy.** The isotropy of `u`,
  `TauCeti.markedIsotropy u P`, consists of the affine automorphisms `f` fixing every point of
  `P` with `u ∘ f = u`. Every such `f` maps the full preimage `u⁻¹(D)` of any set `D` onto itself
  (`TauCeti.image_preimage_eq_of_mem_markedIsotropy`), so the isotropy is contained in the
  stabilizer of the unordered marking `u⁻¹(D)` (`TauCeti.markedIsotropy_le_markingStabilizer`): the
  isotropy of the stabilized map, with its unordered cut marking, is the isotropy of `u`. In
  particular the isotropy of `u` is finite of order dividing `|u⁻¹(D)|!` as soon as `u⁻¹(D)` is
  finite and `P ∪ u⁻¹(D)` contains two distinct points
  (`TauCeti.card_markedIsotropy_dvd_factorial`). This is why the preimage must be taken in full and
  unordered: a chosen subset or an ordering would not be preserved by the isotropy.
* **Finiteness of transverse preimages.** For `K = ℂ`, the map `u` meets `D` transversally at `z`
  (`TauCeti.IsTransverseCutAt u D z`) if near `u z` the set `D` is the zero set of a function
  `g : X → ℂ` such that `g ∘ u` has an invertible real derivative at `z`. For a smooth map `u` to a
  manifold and a local defining function `g` of a codimension-two submanifold `D`, this is the
  injectivity of `dg ∘ du` (`TauCeti.isTransverseCutAt_of_hasMFDerivAt`), that is, the
  transversality of `u` to `D` at `z`. Transverse intersection points are isolated
  (`TauCeti.IsTransverseCutAt.eventually_notMem`). Hence if `u` is continuous, `D` is closed, `u`
  has a limit `y ∉ D` at `∞` and `u` meets `D` transversally at every point of `u⁻¹(D)`, the
  preimage `u⁻¹(D)` is finite (`TauCeti.finite_preimage_of_isTransverseCutAt`). Transversality is
  invariant under reparametrization by maps with invertible derivative
  (`TauCeti.IsTransverseCutAt.comp`), in particular under the automorphisms of the sphere fixing
  `∞` (`TauCeti.isTransverseCutAt_comp_affineEquiv_iff`), so it is a property of the
  unparametrized map.

Nothing here uses that `u` is pseudoholomorphic: for a nonconstant pseudoholomorphic sphere the
finiteness of the isotropy also follows from `MDifferentiable.finite_setOf_comp_eq_iff_exists_ne`,
but the stabilization by a cut bounds its order and identifies it with the automorphism group of
a stable pointed domain.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Section 9.2, on stabilization by the full
  preimage of a codimension-two submanifold transverse to the map.
* K. Cieliebak and K. Mohnke, *Symplectic hypersurfaces and transversality in Gromov–Witten
  theory*, J. Symplectic Geom. 5 (2007), 281–356, on stabilizing domains by the intersection
  points with a hypersurface.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Section 5.1,
  on stable maps and their automorphisms.
-/

public section

noncomputable section

open Filter Set Topology
open scoped Manifold Nat

namespace TauCeti

/-! ### Automorphisms of the sphere preserving a marking -/

section Marking

variable {K : Type*} [Field K] {P C : Set K} {f : K ≃ᵃ[K] K}

/-- The automorphisms of the sphere `K ∪ {∞}` fixing `∞`, fixing each point of `P` and mapping
the unordered marking `C` onto itself: the affine automorphisms `f` of `K` with `f p = p` for
`p ∈ P` and `f '' C = C`. -/
def markingStabilizer (P C : Set K) : Subgroup (K ≃ᵃ[K] K) where
  carrier := {f | (∀ p ∈ P, f p = p) ∧ f '' C = C}
  mul_mem' {f g} hf hg := ⟨fun p hp ↦ by simp [hg.1 p hp, hf.1 p hp], by
    rw [AffineEquiv.coe_mul, Set.image_comp, hg.2, hf.2]⟩
  one_mem' := ⟨fun _ _ ↦ rfl, by simp⟩
  inv_mem' {f} hf := ⟨fun p hp ↦ by rw [AffineEquiv.inv_def, AffineEquiv.symm_apply_eq, hf.1 p hp],
    by
      calc (f⁻¹ : K ≃ᵃ[K] K) '' C = f.symm '' (f '' C) := by rw [hf.2, AffineEquiv.inv_def]
        _ = C := by simp [Set.image_image]⟩

@[simp]
theorem mem_markingStabilizer :
    f ∈ markingStabilizer P C ↔ (∀ p ∈ P, f p = p) ∧ f '' C = C :=
  Iff.rfl

/-- An element of the stabilizer of a marking maps marked points, and only those, to marked
points. -/
theorem apply_mem_iff_of_mem_markingStabilizer (hf : f ∈ markingStabilizer P C) {a : K} :
    f a ∈ C ↔ a ∈ C := by
  conv_lhs => rw [← hf.2]
  exact f.injective.mem_set_image

/-- The permutation of the marking `C` induced by an automorphism preserving it. -/
def markingPerm (P C : Set K) : markingStabilizer P C →* Equiv.Perm C where
  toFun f := f.1.toEquiv.subtypeEquiv fun _ ↦ (apply_mem_iff_of_mem_markingStabilizer f.2).symm
  map_one' := by ext; simp
  map_mul' f g := by ext; simp

@[simp]
theorem coe_markingPerm_apply (f : markingStabilizer P C) (c : C) :
    (markingPerm P C f c : K) = f.1 c :=
  (rfl)

/-- An automorphism of the sphere fixing `∞` and each point of `P`, and preserving the marking
`C`, is determined by the permutation of `C` it induces, provided `P ∪ C` contains two distinct
points. -/
theorem markingPerm_injective (h : ∃ p ∈ P ∪ C, ∃ q ∈ P ∪ C, p ≠ q) :
    Function.Injective (markingPerm P C) := by
  refine (injective_iff_map_eq_one _).2 fun f hf ↦ ?_
  have hfix : ∀ a ∈ P ∪ C, f.1 a = a := by
    rintro a (ha | ha)
    · exact f.2.1 a ha
    · simpa using congrArg Subtype.val (DFunLike.congr_fun hf ⟨a, ha⟩)
  obtain ⟨p, hp, q, hq, hpq⟩ := h
  exact Subtype.ext
    (AffineEquiv.eq_one_of_apply_eq_self_of_apply_eq_self hpq (hfix p hp) (hfix q hq))

/-- **Stability of the stabilized domain.** If the marking `C` is finite and `P ∪ C` contains two
distinct points, the sphere with the special point `∞`, the marked points `P` and the unordered
marking `C` has finitely many automorphisms, and their number divides `|C|!`. -/
theorem card_markingStabilizer_dvd_factorial (hC : C.Finite)
    (h : ∃ p ∈ P ∪ C, ∃ q ∈ P ∪ C, p ≠ q) :
    Nat.card (markingStabilizer P C) ∣ (Nat.card C)! := by
  have := hC.to_subtype
  rw [← Nat.card_perm]
  exact Subgroup.card_dvd_of_injective _ (markingPerm_injective h)

/-- If the marking `C` is finite and `P ∪ C` contains two distinct points, the sphere with the
special point `∞`, the marked points `P` and the unordered marking `C` has finitely many
automorphisms. -/
theorem finite_markingStabilizer (hC : C.Finite) (h : ∃ p ∈ P ∪ C, ∃ q ∈ P ∪ C, p ≠ q) :
    Finite (markingStabilizer P C) :=
  Nat.finite_of_card_ne_zero <| ne_zero_of_dvd_ne_zero (Nat.factorial_ne_zero _)
    (card_markingStabilizer_dvd_factorial hC h)

end Marking

/-! ### The isotropy of a map and its full preimage markings -/

section Isotropy

variable {K : Type*} [Field K] {X : Type*} {u : K → X} {P : Set K} {f : K ≃ᵃ[K] K}

/-- The isotropy group of a map `u` of the sphere `K ∪ {∞}` with the special point `∞` and the
marked points `P`: the affine automorphisms `f` of `K` fixing each point of `P` with
`u ∘ f = u`. -/
def markedIsotropy (u : K → X) (P : Set K) : Subgroup (K ≃ᵃ[K] K) where
  carrier := {f | (∀ p ∈ P, f p = p) ∧ u ∘ f = u}
  mul_mem' {f g} hf hg := ⟨fun p hp ↦ by simp [hg.1 p hp, hf.1 p hp], by
    rw [AffineEquiv.coe_mul, ← Function.comp_assoc, hf.2, hg.2]⟩
  one_mem' := ⟨fun _ _ ↦ rfl, rfl⟩
  inv_mem' {f} hf := ⟨fun p hp ↦ by rw [AffineEquiv.inv_def, AffineEquiv.symm_apply_eq, hf.1 p hp],
    by
      funext z
      simpa [AffineEquiv.inv_def] using congrFun hf.2 (f.symm z) |>.symm⟩

@[simp]
theorem mem_markedIsotropy : f ∈ markedIsotropy u P ↔ (∀ p ∈ P, f p = p) ∧ u ∘ f = u :=
  Iff.rfl

/-- Without marked points besides `∞`, the isotropy is the set of affine automorphisms `f` with
`u ∘ f = u`. -/
@[simp]
theorem coe_markedIsotropy_empty :
    (markedIsotropy u ∅ : Set (K ≃ᵃ[K] K)) = {f : K ≃ᵃ[K] K | u ∘ f = u} := by
  ext f
  simp

/-- An element of the isotropy of `u` maps the full preimage `u⁻¹(D)` of any set onto itself. -/
theorem image_preimage_eq_of_mem_markedIsotropy (hf : f ∈ markedIsotropy u P) (D : Set X) :
    f '' (u ⁻¹' D) = u ⁻¹' D := by
  have h : f ⁻¹' (u ⁻¹' D) = u ⁻¹' D := by rw [← Set.preimage_comp, hf.2]
  conv_lhs => rw [← h]
  exact Set.image_preimage_eq _ f.surjective

/-- **Forgetting the cut points.** The isotropy of `u` preserves the unordered marking by the full
preimage of any set `D`, so the isotropy of the map with this marking is the isotropy of `u`. -/
theorem markedIsotropy_le_markingStabilizer (D : Set X) :
    markedIsotropy u P ≤ markingStabilizer P (u ⁻¹' D) :=
  fun _ hf ↦ ⟨hf.1, image_preimage_eq_of_mem_markedIsotropy hf D⟩

/-- **Stabilization bounds the isotropy.** If the full preimage `u⁻¹(D)` is finite and
`P ∪ u⁻¹(D)` contains two distinct points, the isotropy of `u` is finite of order dividing
`|u⁻¹(D)|!`. -/
theorem card_markedIsotropy_dvd_factorial {D : Set X} (hD : (u ⁻¹' D).Finite)
    (h : ∃ p ∈ P ∪ u ⁻¹' D, ∃ q ∈ P ∪ u ⁻¹' D, p ≠ q) :
    Nat.card (markedIsotropy u P) ∣ (Nat.card (u ⁻¹' D))! :=
  (Subgroup.card_dvd_of_le (markedIsotropy_le_markingStabilizer D)).trans
    (card_markingStabilizer_dvd_factorial hD h)

/-- If the full preimage `u⁻¹(D)` is finite and `P ∪ u⁻¹(D)` contains two distinct points, the
isotropy of `u` is finite. -/
theorem finite_markedIsotropy {D : Set X} (hD : (u ⁻¹' D).Finite)
    (h : ∃ p ∈ P ∪ u ⁻¹' D, ∃ q ∈ P ∪ u ⁻¹' D, p ≠ q) :
    Finite (markedIsotropy u P) :=
  Nat.finite_of_card_ne_zero <| ne_zero_of_dvd_ne_zero (Nat.factorial_ne_zero _)
    (card_markedIsotropy_dvd_factorial hD h)

end Isotropy

/-! ### Transverse target cuts -/

section Transverse

variable {X : Type*} [TopologicalSpace X] {u : ℂ → X} {D : Set X} {z : ℂ}

/-- The map `u` meets the target cut `D` transversally at `z`: near `u z` the set `D` is the zero
set of a function `g : X → ℂ` such that `g ∘ u` has an invertible real derivative at `z`. The
predicate is used at the points `z` of `u⁻¹(D)`. There, for a smooth map to a manifold and a local
defining function `g` of a codimension-two submanifold `D`, it is the transversality of `u` to `D`
at `z` (`TauCeti.isTransverseCutAt_of_hasMFDerivAt`). -/
def IsTransverseCutAt (u : ℂ → X) (D : Set X) (z : ℂ) : Prop :=
  ∃ (g : X → ℂ) (L : ℂ ≃L[ℝ] ℂ), (∀ᶠ x in 𝓝 (u z), x ∈ D ↔ g x = 0) ∧
    HasFDerivAt (g ∘ u) (L : ℂ →L[ℝ] ℂ) z

/-- A transverse intersection point of `u` with `D` is isolated: nearby points are not mapped
into `D`. -/
theorem IsTransverseCutAt.eventually_notMem (h : IsTransverseCutAt u D z)
    (hu : ContinuousAt u z) : ∀ᶠ w in 𝓝[≠] z, u w ∉ D := by
  obtain ⟨g, L, hD, hg⟩ := h
  filter_upwards [hg.eventually_ne (c := 0) ⟨_, L.antilipschitzWith⟩,
    nhdsWithin_le_nhds (hu.eventually hD)] with w hw hwD
  exact fun hmem ↦ hw (hwD.1 hmem)

/-- **Finiteness of the full preimage of a transverse cut.** If the sphere component `u`, with a
limit `y ∉ D` at `∞`, meets the closed set `D` transversally at every point of `u⁻¹(D)`, then
`u⁻¹(D)` is finite. -/
theorem finite_preimage_of_isTransverseCutAt {y : X} (hu : Continuous u) (hD : IsClosed D)
    (hy : Tendsto u (cocompact ℂ) (𝓝 y)) (hyD : y ∉ D)
    (h : ∀ z ∈ u ⁻¹' D, IsTransverseCutAt u D z) : (u ⁻¹' D).Finite := by
  obtain ⟨K, hK, hKD⟩ := mem_cocompact.1 (hy (hD.isOpen_compl.mem_nhds hyD))
  refine (hK.of_isClosed_subset (hD.preimage hu) fun z hz ↦ ?_).finite
    (isDiscrete_iff_nhdsNE.2 fun z hz ↦
      inf_principal_eq_bot.2 ((h z hz).eventually_notMem hu.continuousAt))
  by_contra hzK
  exact hKD hzK hz

/-- Transversality is invariant under reparametrization by a map with invertible derivative. -/
theorem IsTransverseCutAt.comp {ρ : ℂ → ℂ} (h : IsTransverseCutAt u D (ρ z)) {E : ℂ ≃L[ℝ] ℂ}
    (hρ : HasFDerivAt ρ (E : ℂ →L[ℝ] ℂ) z) : IsTransverseCutAt (u ∘ ρ) D z := by
  obtain ⟨g, L, hD, hg⟩ := h
  refine ⟨g, E.trans L, hD, ?_⟩
  rw [← ContinuousLinearEquiv.comp_coe]
  exact hg.comp z hρ

/-- Transversality to a target cut is invariant under the automorphisms of the sphere fixing `∞`,
so it is a property of the unparametrized map. -/
theorem isTransverseCutAt_comp_affineEquiv_iff (f : ℂ ≃ᵃ[ℂ] ℂ) :
    IsTransverseCutAt (u ∘ f) D z ↔ IsTransverseCutAt u D (f z) := by
  -- An affine automorphism `w ↦ f.linear w + f 0` of `ℂ` has the invertible real derivative
  -- `f.linear`, read over `ℝ`.
  have hderiv (f : ℂ ≃ᵃ[ℂ] ℂ) (z : ℂ) : ∃ E : ℂ ≃L[ℝ] ℂ, HasFDerivAt f (E : ℂ →L[ℝ] ℂ) z := by
    refine ⟨f.linear.toContinuousLinearEquiv.restrictScalars ℝ, ?_⟩
    convert ((f.linear.toContinuousLinearEquiv.hasFDerivAt (x := z)).restrictScalars ℝ).add_const
      (f 0) using 1
    · funext w
      exact f.apply_eq_linear_add w
    · ext w
      simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨E, hE⟩ := hderiv f.symm (f z)
    have h' : IsTransverseCutAt (u ∘ f) D (f.symm (f z)) := by simpa using h
    have hu : (u ∘ f) ∘ f.symm = u := by
      funext w
      simp
    simpa [hu] using IsTransverseCutAt.comp h' hE
  · obtain ⟨E, hE⟩ := hderiv f z
    exact IsTransverseCutAt.comp h hE

/-- Transversality of a smooth map `u` from `ℂ` to a manifold to a set `D` with a local defining
function `g` at `u z`: if `d(g ∘ u) = dg ∘ du` is injective at `z`, then `u` meets the target cut
`D` transversally at `z`. -/
theorem isTransverseCutAt_of_hasMFDerivAt {E H M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
    [ChartedSpace H M] {u : ℂ → M} {D : Set M} {g : M → ℂ}
    {dg : TangentSpace I (u z) →L[ℝ] ℂ} {du : ℂ →L[ℝ] TangentSpace I (u z)}
    (hD : ∀ᶠ x in 𝓝 (u z), x ∈ D ↔ g x = 0) (hg : HasMFDerivAt I 𝓘(ℝ, ℂ) g (u z) dg)
    (hu : HasMFDerivAt 𝓘(ℝ, ℂ) I u z du) (hinj : Function.Injective (dg.comp du)) :
    IsTransverseCutAt u D z := by
  refine ⟨g, (LinearEquiv.ofInjectiveEndo (dg.comp du : ℂ →ₗ[ℝ] ℂ) hinj).toContinuousLinearEquiv,
    hD, ?_⟩
  have he : ((LinearEquiv.ofInjectiveEndo (dg.comp du : ℂ →ₗ[ℝ] ℂ) hinj).toContinuousLinearEquiv :
      ℂ →L[ℝ] ℂ) = dg.comp du := by
    ext w
    simp
  rw [he]
  exact hasMFDerivAt_iff_hasFDerivAt.1 (hg.comp z hu)

end Transverse

end TauCeti
