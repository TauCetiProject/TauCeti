/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.LinearAlgebra.BilinearForm.Contact
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.Dimension.Prod

/-!
# The linear normal form of a contact covector along a Legendrian subspace

Let `a` be a covector on a finite-dimensional space `V` which is contact for an alternating form
`B` (`Module.Dual.IsContact`), with Reeb vector `r = a.reebVector B`. A linear map `f : U → V` is
**Legendrian** (`Module.Dual.IsLegendrian`) when it is injective, takes values in `ker a`, `B`
vanishes on its image, and `2 dim U + 1 = dim V`. This is the linear algebra of a Legendrian
submanifold `Λ` of a contact manifold `(M, α)` at a point `x`: `f = dι_x`, `a = α_x` and
`B = dα_x`.

The linear model of a neighbourhood of the zero section of the one-jet space `J¹U = T^*U × ℝ` is
`U × U^* × K`, with coordinates `(q, p, z)`, carrying the values along the zero section of the
contact form `dz - p dq` and of its exterior derivative `dq ∧ dp`:

`(q, p, z) ↦ z` (`TauCeti.jetContactCovector`) and
`((q, p, z), (q', p', z')) ↦ p' q - p q'` (`TauCeti.jetContactBilinForm`).

The zero section `q ↦ (q, 0, 0)` is Legendrian for these data
(`TauCeti.isLegendrian_jetContactCovector_inl`). This file proves that every Legendrian map is of
this form: there is a linear equivalence `e : U × U^* × K ≃ V` with

`e (q, 0, 0) = f q`, `a ∘ e = dz`, `B (e ·) (e ·) = dq ∧ dp`

(`Module.Dual.IsLegendrian.exists_linearEquiv_jetContact`). So the full first-order contact data
of a contact manifold along a Legendrian submanifold, the value of the contact form and of its
exterior derivative on the whole ambient tangent space, agree with those of the one-jet model
along its zero section after a linear identification which is the identity on the Legendrian
directions. This is the first-order input of the strict Legendrian neighbourhood theorem, in which
the two contact forms are then interpolated and joined by a strict Moser isotopy.

The identification is constructed explicitly. The **contact pairing** of `f`
(`Module.Dual.contactPairing`), `v ↦ (B (f ·) v, a v) ∈ U^* × K`, has kernel the image of `f`
(`Module.Dual.IsLegendrian.ker_contactPairing`) and is surjective. Its quotient map
`V / f(U) ≃ U^* × K` is the linear form of the identification of the normal bundle of a
Legendrian submanifold with `T^*Λ × ℝ`
(`TauCeti.SmoothEmbedding.normalSpaceEquivOfIsLegendrianImmersion`).
Given any linear `s : U^* → V` with `a.contactPairing B f (s p) = (p, 0)`, the map

`(q, p, z) ↦ f (q + ℓ p) + s p + z r`, where `p' (ℓ p) = -½ B (s p) (s p')`,

(`Module.Dual.jetMap`) is such a linear equivalence. The Reeb vector is `B`-orthogonal to
everything, so it may carry the `z`-direction, and the correction `ℓ`, valued in the image of `f`,
makes the span of `s` and `r` isotropic for `B`. It is an explicit formula in `f`, `s`, `B` and
`r`, with no choice of basis, and it uses that `2` is invertible in `K`.

Every such normal form carries the contact pairing to the projection `(q, p, z) ↦ (p, z)`
(`Module.Dual.contactPairing_apply_eq_snd`) and sends `∂_z = (0, 0, 1)` to the Reeb vector
(`Module.Dual.IsContact.apply_eq_reebVector`). Two normal forms differ by a symmetric shear
`(q, p, z) ↦ (q + S p, p, z)` with `p' (S p) = p (S p')`
(`Module.Dual.IsContact.exists_symm_apply_eq`), so the normal form is unique up to the choice of
a Lagrangian complement of `f(U)` in `ker a`.

## Main declarations

* `TauCeti.jetContactCovector`, `TauCeti.jetContactBilinForm`: the one-jet model.
* `Module.Dual.IsLegendrian`: Legendrian linear maps.
* `Module.Dual.contactPairing`: the contact pairing `v ↦ (B (f ·) v, a v)`.
* `Module.Dual.IsLegendrian.ker_contactPairing`,
  `Module.Dual.IsLegendrian.range_contactPairing`: its kernel is the image of `f`, and it is
  surjective.
* `Module.Dual.jetMap`: the explicit normal form built from a section `s` of the contact pairing.
* `Module.Dual.IsLegendrian.exists_linearEquiv_jetContact`,
  `Module.Dual.isLegendrian_iff_exists_linearEquiv_jetContact`: the linear normal form.
* `Module.Dual.IsContact.exists_symm_apply_eq`: uniqueness up to symmetric shears.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 2.5 (neighbourhoods of Legendrian submanifolds).
* A. Kriegl, P. W. Michor, *The Convenient Setting of Global Analysis*, Mathematical Surveys and
  Monographs 53, AMS (1997), Proposition 43.18.
-/

public section

open Module

namespace Module.Dual

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  {a : Module.Dual K V} {B : LinearMap.BilinForm K V} {f : U →ₗ[K] V}

/-- A linear map `f : U → V` is **Legendrian** for a covector `a` and a bilinear form `B` on `V`
when it is injective, takes values in `ker a`, `B` vanishes on its image, and
`2 dim U + 1 = dim V`. When `a` is contact for `B`, its image is a maximal subspace of `ker a` on
which `B` vanishes (`Module.Dual.IsContact.two_mul_finrank_add_one_le`). For a Legendrian
submanifold `Λ` of a contact manifold `(M, α)`, the differential of the inclusion at `x` is
Legendrian for `α_x` and `dα_x`. -/
structure IsLegendrian (a : Module.Dual K V) (B : LinearMap.BilinForm K V) (f : U →ₗ[K] V) :
    Prop where
  /-- A Legendrian map is injective. -/
  injective : Function.Injective f
  /-- A Legendrian map takes values in `ker a`. -/
  apply_eq_zero (u : U) : a (f u) = 0
  /-- The bilinear form vanishes on the image of a Legendrian map. -/
  apply_apply_eq_zero (u u' : U) : B (f u) (f u') = 0
  /-- The dimension count `2 dim U + 1 = dim V`. -/
  two_mul_finrank_add_one : 2 * finrank K U + 1 = finrank K V

/-- The target of a Legendrian map is finite-dimensional, since its dimension `2 dim U + 1` is
positive. -/
theorem IsLegendrian.finiteDimensional (hf : a.IsLegendrian B f) : FiniteDimensional K V :=
  Module.finite_of_finrank_pos (hf.two_mul_finrank_add_one ▸ Nat.succ_pos _)

end Module.Dual

namespace TauCeti

section Model

variable (K U : Type*) [CommRing K] [AddCommGroup U] [Module K U]

/-- The **one-jet contact covector** `dz` on `U × U^* × K`, with coordinates `(q, p, z)`. It is
the value along the zero section of the contact form `dz - p dq` of the one-jet space
`T^*U × K`. -/
def jetContactCovector : Module.Dual K (U × Module.Dual K U × K) :=
  LinearMap.snd K (Module.Dual K U) K ∘ₗ LinearMap.snd K U (Module.Dual K U × K)

@[simp]
theorem jetContactCovector_apply (x : U × Module.Dual K U × K) :
    jetContactCovector K U x = x.2.2 :=
  (rfl)

/-- The **one-jet contact bilinear form** `dq ∧ dp` on `U × U^* × K`, with coordinates
`(q, p, z)`: `((q, p, z), (q', p', z')) ↦ p' q - p q'`. It is the value along the zero section of
the exterior derivative of the contact form `dz - p dq`. -/
def jetContactBilinForm : LinearMap.BilinForm K (U × Module.Dual K U × K) :=
  (Module.Dual.eval K U).compl₁₂ (LinearMap.fst K U _)
      (LinearMap.fst K _ K ∘ₗ LinearMap.snd K U (Module.Dual K U × K)) -
    (LinearMap.id : Module.Dual K U →ₗ[K] Module.Dual K U).compl₁₂
      (LinearMap.fst K _ K ∘ₗ LinearMap.snd K U (Module.Dual K U × K)) (LinearMap.fst K U _)

@[simp]
theorem jetContactBilinForm_apply (x y : U × Module.Dual K U × K) :
    jetContactBilinForm K U x y = y.2.1 x.1 - x.2.1 y.1 :=
  (rfl)

/-- The one-jet contact bilinear form is alternating. -/
theorem isAlt_jetContactBilinForm : (jetContactBilinForm K U).IsAlt := fun x ↦ by
  rw [jetContactBilinForm_apply, sub_self]

end Model

variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U]

/-- The one-jet contact covector `dz` is contact for the one-jet bilinear form `dq ∧ dp`. -/
theorem isContact_jetContactCovector (K U : Type*) [Field K] [AddCommGroup U] [Module K U] :
    (jetContactCovector K U).IsContact (jetContactBilinForm K U) := by
  refine (Module.Dual.isContact_iff_of_isRefl (isAlt_jetContactBilinForm K U).isRefl).2
    ⟨fun h ↦ by simpa using LinearMap.congr_fun h (0, 0, 1), fun v hv hvw ↦ ?_⟩
  -- Test `v` against the kernel vectors `(0, p, 0)` and `(u, 0, 0)`.
  have hq : v.1 = 0 := (Module.forall_dual_apply_eq_zero_iff K v.1).1 fun p ↦ by
    simpa using hvw (0, p, 0) rfl
  have hp : v.2.1 = 0 := LinearMap.ext fun u ↦ by simpa using hvw (u, 0, 0) rfl
  exact Prod.ext hq (Prod.ext hp (by simpa using hv))

/-- The Reeb vector of the one-jet contact covector is `∂_z = (0, 0, 1)`. -/
@[simp]
theorem reebVector_jetContactCovector [FiniteDimensional K U] :
    (jetContactCovector K U).reebVector (jetContactBilinForm K U) = (0, 0, 1) :=
  ((isContact_jetContactCovector K U).eq_reebVector_iff_of_isAlt
    (isAlt_jetContactBilinForm K U)).2
    ⟨by simp, LinearMap.ext fun w ↦ by simp⟩ |>.symm

/-- The zero section `q ↦ (q, 0, 0)` of the one-jet model is Legendrian. -/
theorem isLegendrian_jetContactCovector_inl [FiniteDimensional K U] :
    (jetContactCovector K U).IsLegendrian (jetContactBilinForm K U)
      (LinearMap.inl K U (Module.Dual K U × K)) where
  injective := LinearMap.inl_injective
  apply_eq_zero _ := by simp
  apply_apply_eq_zero _ _ := by simp
  two_mul_finrank_add_one := (Module.finrank_prod_dual_prod_self K U).symm

end TauCeti

namespace Module.Dual

open TauCeti

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
  {a : Module.Dual K V} {B : LinearMap.BilinForm K V} {f : U →ₗ[K] V}

/-! ### The contact pairing -/

/-- The **contact pairing** of a linear map `f : U → V`, the linear map `v ↦ (B (f ·) v, a v)`
from `V` to `U^* × K`. For the differential of a Legendrian embedding, with `a = α_x` and
`B = dα_x`, this is `TauCeti.SmoothEmbedding.contactPairing`. -/
def contactPairing (a : Module.Dual K V) (B : LinearMap.BilinForm K V) (f : U →ₗ[K] V) :
    V →ₗ[K] Module.Dual K U × K :=
  (B.flip.compl₂ f).prod a

@[simp]
theorem contactPairing_apply_fst_apply (v : V) (u : U) :
    (a.contactPairing B f v).1 u = B (f u) v :=
  (rfl)

@[simp]
theorem contactPairing_apply_snd (v : V) : (a.contactPairing B f v).2 = a v :=
  (rfl)

/-- The contact pairing of a Legendrian map vanishes on its image. -/
theorem IsLegendrian.contactPairing_apply (hf : a.IsLegendrian B f) (u : U) :
    a.contactPairing B f (f u) = 0 :=
  Prod.ext (LinearMap.ext fun u' ↦ hf.apply_apply_eq_zero u' u) (hf.apply_eq_zero u)

/-- **The kernel of the contact pairing is the Legendrian subspace.** A vector `v` with `a v = 0`
and `B (f u) v = 0` for all `u` spans, together with the image of `f`, a subspace of `ker a` on
which `B` vanishes, and the image of `f` is already maximal among those. -/
theorem IsLegendrian.ker_contactPairing (hB : B.IsAlt) (h : a.IsContact B)
    (hf : a.IsLegendrian B f) : LinearMap.ker (a.contactPairing B f) = LinearMap.range f := by
  have := hf.finiteDimensional
  refine le_antisymm (fun v hv ↦ ?_)
    (LinearMap.range_le_ker_iff.2 (LinearMap.ext hf.contactPairing_apply))
  have hva : a v = 0 := congrArg Prod.snd (LinearMap.mem_ker.1 hv)
  have hvB (u : U) : B (f u) v = 0 :=
    LinearMap.congr_fun (congrArg Prod.fst (LinearMap.mem_ker.1 hv)) u
  have hvB' (u : U) : B v (f u) = 0 := by rw [← hB.neg_eq, hvB, neg_zero]
  set W := LinearMap.range f ⊔ Submodule.span K {v}
  have hWa : W ≤ LinearMap.ker a :=
    sup_le (by rintro _ ⟨u, rfl⟩; exact LinearMap.mem_ker.2 (hf.apply_eq_zero u))
      ((Submodule.span_singleton_le_iff_mem _ _).2 (LinearMap.mem_ker.2 hva))
  have hWB : ∀ w ∈ W, ∀ w' ∈ W, B w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hw
    obtain ⟨y', hy', z', hz', rfl⟩ := Submodule.mem_sup.1 hw'
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.1 hy
    obtain ⟨u', rfl⟩ := LinearMap.mem_range.1 hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hz'
    simp [hf.apply_apply_eq_zero, hvB, hvB', hB v]
  -- The dimension bound for isotropic subspaces of `ker a` forces `W = range f`.
  have hdim := h.two_mul_finrank_add_one_le hWa hWB
  have hrange : finrank K (LinearMap.range f) = finrank K U :=
    LinearMap.finrank_range_of_inj hf.injective
  have hW : LinearMap.range f = W := Submodule.eq_of_le_of_finrank_le le_sup_left (by
    have := hf.two_mul_finrank_add_one
    omega)
  rw [hW]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

/-- **The contact pairing of a Legendrian map is surjective**, by the dimension count
`dim V - dim U = dim U^* + 1`. -/
theorem IsLegendrian.range_contactPairing (hB : B.IsAlt) (h : a.IsContact B)
    (hf : a.IsLegendrian B f) : LinearMap.range (a.contactPairing B f) = ⊤ := by
  have := hf.finiteDimensional
  have : FiniteDimensional K U := Module.Finite.of_injective f hf.injective
  refine Submodule.eq_top_of_finrank_eq ?_
  have hrk := LinearMap.finrank_range_add_finrank_ker (a.contactPairing B f)
  rw [hf.ker_contactPairing hB h, LinearMap.finrank_range_of_inj hf.injective] at hrk
  rw [finrank_prod, Subspace.dual_finrank_eq, finrank_self]
  have := hf.two_mul_finrank_add_one
  omega

/-- A Legendrian map has a linear section of its contact pairing over `U^* × {0}`: a linear
`s : U^* → V` with `a (s p) = 0` and `B (f u) (s p) = p u`. -/
theorem IsLegendrian.exists_contactPairing_eq (hB : B.IsAlt) (h : a.IsContact B)
    (hf : a.IsLegendrian B f) :
    ∃ s : Module.Dual K U →ₗ[K] V, ∀ p, a.contactPairing B f (s p) = (p, 0) := by
  obtain ⟨g, hg⟩ :=
    (a.contactPairing B f).exists_rightInverse_of_surjective (hf.range_contactPairing hB h)
  exact ⟨g ∘ₗ LinearMap.inl K _ K, fun p ↦ by simpa using LinearMap.congr_fun hg (p, 0)⟩

/-! ### The explicit normal form -/

section JetMap

variable [FiniteDimensional K U] {s : Module.Dual K U →ₗ[K] V}

/-- The **one-jet normal form** of `f` built from a linear map `s : U^* → V`:

`(q, p, z) ↦ f (q + ℓ p) + s p + z r`,

where `r` is the Reeb vector of `a` and `ℓ p ∈ U` is determined by
`p' (ℓ p) = -½ B (s p) (s p')`.
When `f` is Legendrian and `s` is a section of the contact pairing over `U^* × {0}`, this is a
linear equivalence carrying the one-jet model to `(a, B)`
(`Module.Dual.IsLegendrian.apply_jetMap`, `Module.Dual.IsLegendrian.apply_jetMap_jetMap`,
`Module.Dual.IsLegendrian.bijective_jetMap`). -/
noncomputable def jetMap (a : Module.Dual K V) (B : LinearMap.BilinForm K V) (f : U →ₗ[K] V)
    (s : Module.Dual K U →ₗ[K] V) : U × Module.Dual K U × K →ₗ[K] V :=
  f ∘ₗ (LinearMap.fst K U _ + (evalEquiv K U).symm.toLinearMap ∘ₗ
      ((-(2 : K)⁻¹) • B.compl₁₂ s s) ∘ₗ
        LinearMap.fst K _ K ∘ₗ LinearMap.snd K U _) +
    s ∘ₗ LinearMap.fst K _ K ∘ₗ LinearMap.snd K U _ +
    (LinearMap.snd K _ K ∘ₗ LinearMap.snd K U (Module.Dual K U × K)).smulRight (a.reebVector B)

theorem jetMap_apply (x : U × Module.Dual K U × K) :
    a.jetMap B f s x =
      f (x.1 + (evalEquiv K U).symm ((-(2 : K)⁻¹) • B.compl₁₂ s s x.2.1)) + s x.2.1 +
        x.2.2 • a.reebVector B :=
  (rfl)

/-- The one-jet normal form restricts to `f` on the zero section. -/
@[simp]
theorem jetMap_inl (q : U) : a.jetMap B f s (q, 0, 0) = f q := by
  simp [jetMap_apply]

variable (hs : ∀ p, a.contactPairing B f (s p) = (p, 0))
include hs

/-- The one-jet normal form pulls `a` back to `dz`. -/
theorem IsLegendrian.apply_jetMap (h : a.IsContact B) (hf : a.IsLegendrian B f)
    (x : U × Module.Dual K U × K) : a (a.jetMap B f s x) = x.2.2 := by
  have := hf.finiteDimensional
  have hsa : a (s x.2.1) = 0 := by simpa using congrArg Prod.snd (hs x.2.1)
  simp [jetMap_apply, hf.apply_eq_zero, hsa, h.apply_reebVector]

/-- The one-jet normal form carries the contact pairing to the projection `(q, p, z) ↦ (p, z)`. -/
theorem IsLegendrian.contactPairing_jetMap (hB : B.IsAlt) (h : a.IsContact B)
    (hf : a.IsLegendrian B f) (x : U × Module.Dual K U × K) :
    a.contactPairing B f (a.jetMap B f s x) = x.2 := by
  have := hf.finiteDimensional
  rw [jetMap_apply, map_add, map_add, hf.contactPairing_apply, zero_add, hs, map_smul]
  refine Prod.ext (LinearMap.ext fun u ↦ ?_) ?_
  · simp [h.apply_reebVector_right hB]
  · simp [h.apply_reebVector]

/-- **The one-jet normal form pulls `B` back to `dq ∧ dp`.** The Reeb vector is `B`-orthogonal
to everything, `B (f u) (s p) = p u`, and the correction `ℓ` cancels the values
`B (s p) (s p')`. -/
theorem IsLegendrian.apply_jetMap_jetMap [NeZero (2 : K)] (hB : B.IsAlt) (h : a.IsContact B)
    (hf : a.IsLegendrian B f) (x y : U × Module.Dual K U × K) :
    B (a.jetMap B f s x) (a.jetMap B f s y) = jetContactBilinForm K U x y := by
  have := hf.finiteDimensional
  have hsB (u : U) (p : Module.Dual K U) : B (f u) (s p) = p u := by
    simpa using LinearMap.congr_fun (congrArg Prod.fst (hs p)) u
  have hsB' (u : U) (p : Module.Dual K U) : B (s p) (f u) = -p u := by
    rw [← hB.neg_eq, hsB]
  have hβ : B (s y.2.1) (s x.2.1) = -B (s x.2.1) (s y.2.1) := (hB.neg_eq _ _).symm
  have h2 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ two_ne_zero
  simp only [jetMap_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    hf.apply_apply_eq_zero, hsB, hsB', h.apply_reebVector_left hB,
    h.apply_reebVector_right hB, apply_evalEquiv_symm_apply, LinearMap.compl₁₂_apply,
    smul_eq_mul, mul_zero, add_zero, zero_add, jetContactBilinForm_apply]
  linear_combination (2 : K)⁻¹ * hβ - B (s x.2.1) (s y.2.1) * h2

/-- The one-jet normal form of a Legendrian map is injective: the contact pairing recovers
`(p, z)`, and then `f` recovers `q`. -/
theorem IsLegendrian.injective_jetMap (hB : B.IsAlt) (h : a.IsContact B)
    (hf : a.IsLegendrian B f) : Function.Injective (a.jetMap B f s) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have h2 : x.2 = 0 := by
    rw [← hf.contactPairing_jetMap hs hB h, hx, map_zero]
  obtain ⟨q, p, z⟩ := x
  obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 h2
  have hq : f q = 0 := by simpa using hx
  simp [hf.injective (hq.trans (map_zero f).symm)]

/-- The one-jet normal form of a Legendrian map is a linear isomorphism onto `V`. -/
theorem IsLegendrian.bijective_jetMap (hB : B.IsAlt) (h : a.IsContact B)
    (hf : a.IsLegendrian B f) : Function.Bijective (a.jetMap B f s) := by
  have := hf.finiteDimensional
  have hinj := hf.injective_jetMap hs hB h
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [Module.finrank_prod_dual_prod_self, hf.two_mul_finrank_add_one]

end JetMap

/-! ### The normal form -/

/-- **Linear normal form along a Legendrian subspace.** If `a` is contact for an alternating form
`B` on a finite-dimensional space `V` and `f : U → V` is Legendrian, there is a linear
equivalence `e : U × U^* × K ≃ V` which restricts to `f` on the zero section `U × {0} × {0}`,
pulls `a` back to `dz` and pulls `B` back to `dq ∧ dp`. One such equivalence is the explicit
`Module.Dual.jetMap`. -/
theorem IsLegendrian.exists_linearEquiv_jetContact [NeZero (2 : K)] (hB : B.IsAlt)
    (h : a.IsContact B) (hf : a.IsLegendrian B f) :
    ∃ e : (U × Module.Dual K U × K) ≃ₗ[K] V,
      e.toLinearMap ∘ₗ LinearMap.inl K U _ = f ∧
        a ∘ₗ e.toLinearMap = jetContactCovector K U ∧
          B.compl₁₂ e.toLinearMap e.toLinearMap = jetContactBilinForm K U := by
  have := hf.finiteDimensional
  have : FiniteDimensional K U := Module.Finite.of_injective f hf.injective
  obtain ⟨s, hs⟩ := hf.exists_contactPairing_eq hB h
  refine ⟨LinearEquiv.ofBijective _ (hf.bijective_jetMap hs hB h), LinearMap.ext fun q ↦ ?_,
    LinearMap.ext fun x ↦ ?_, LinearMap.ext₂ fun x y ↦ ?_⟩
  · exact jetMap_inl q
  · simpa using hf.apply_jetMap hs h x
  · simpa using hf.apply_jetMap_jetMap hs hB h x y

/-- **Legendrian maps are those with one-jet coordinates.** For a contact covector `a` of an
alternating form `B` on a finite-dimensional space, a linear map `f` is Legendrian exactly when
some linear equivalence `e : U × U^* × K ≃ V` restricts to `f` on the zero section, pulls `a`
back to `dz` and pulls `B` back to `dq ∧ dp`. -/
theorem isLegendrian_iff_exists_linearEquiv_jetContact [NeZero (2 : K)] [FiniteDimensional K V]
    (hB : B.IsAlt) (h : a.IsContact B) :
    a.IsLegendrian B f ↔ ∃ e : (U × Module.Dual K U × K) ≃ₗ[K] V,
      e.toLinearMap ∘ₗ LinearMap.inl K U _ = f ∧
        a ∘ₗ e.toLinearMap = jetContactCovector K U ∧
          B.compl₁₂ e.toLinearMap e.toLinearMap = jetContactBilinForm K U := by
  refine ⟨IsLegendrian.exists_linearEquiv_jetContact hB h, ?_⟩
  rintro ⟨e, rfl, ha, hB'⟩
  have hinj : Function.Injective
      (e.toLinearMap ∘ₗ LinearMap.inl K U _) :=
    e.injective.comp LinearMap.inl_injective
  have : FiniteDimensional K U := Module.Finite.of_injective _ hinj
  refine ⟨hinj, fun u ↦ ?_, fun u u' ↦ ?_, ?_⟩
  · simpa [Prod.mk_zero_zero] using LinearMap.congr_fun ha (u, 0, 0)
  · simpa [Prod.mk_zero_zero] using LinearMap.congr_fun₂ hB' (u, 0, 0) (u', 0, 0)
  · rw [← Module.finrank_prod_dual_prod_self, e.finrank_eq]

/-! ### Properties of every normal form -/

/-- **A one-jet normal form identifies the contact pairing with the projection** `(q, p, z) ↦
(p, z)`. So the normal map it induces on `V / f(U)` is the canonical identification
`[v] ↦ (B (f ·) v, a v)` with `U^* × K`, whichever normal form is chosen. -/
theorem contactPairing_apply_eq_snd {e : U × Module.Dual K U × K →ₗ[K] V}
    (he : e ∘ₗ LinearMap.inl K U _ = f) (ha : a ∘ₗ e = jetContactCovector K U)
    (hB' : B.compl₁₂ e e = jetContactBilinForm K U) (x : U × Module.Dual K U × K) :
    a.contactPairing B f (e x) = x.2 := by
  subst he
  refine Prod.ext (LinearMap.ext fun u ↦ ?_) ?_
  · simpa [Prod.mk_zero_zero] using LinearMap.congr_fun₂ hB' (u, 0, 0) x
  · simpa using LinearMap.congr_fun ha x

/-- **A one-jet normal form sends `∂_z` to the Reeb vector.** -/
theorem IsContact.apply_eq_reebVector [FiniteDimensional K V] (hB : B.IsAlt) (h : a.IsContact B)
    (e : (U × Module.Dual K U × K) ≃ₗ[K] V)
    (ha : a ∘ₗ e.toLinearMap = jetContactCovector K U)
    (hB' : B.compl₁₂ e.toLinearMap e.toLinearMap = jetContactBilinForm K U) :
    e (0, 0, 1) = a.reebVector B := by
  refine (h.eq_reebVector_iff_of_isAlt hB).2 ⟨by simpa using LinearMap.congr_fun ha (0, 0, 1),
    LinearMap.ext fun w ↦ ?_⟩
  obtain ⟨y, rfl⟩ := e.surjective w
  simpa using LinearMap.congr_fun₂ hB' (0, 0, 1) y

/-- **One-jet normal forms are unique up to symmetric shears.** Two linear equivalences
`e, e' : U × U^* × K ≃ V` restricting to the same `f` on the zero section and pulling `a` back
to `dz` and `B` back to `dq ∧ dp` differ by a shear `(q, p, z) ↦ (q + S p, p, z)`, where
`S : U^* → U` is symmetric, `p' (S p) = p (S p')`. The image of `{0} × U^* × {0}` under a normal
form is a Lagrangian complement of `f(U)` in `ker a`, and `S` records the change of complement. -/
theorem IsContact.exists_symm_apply_eq [FiniteDimensional K V] (hB : B.IsAlt) (h : a.IsContact B)
    {e e' : (U × Module.Dual K U × K) ≃ₗ[K] V}
    (he : e.toLinearMap ∘ₗ LinearMap.inl K U _ = f)
    (ha : a ∘ₗ e.toLinearMap = jetContactCovector K U)
    (hB' : B.compl₁₂ e.toLinearMap e.toLinearMap = jetContactBilinForm K U)
    (he' : e'.toLinearMap ∘ₗ LinearMap.inl K U _ = f)
    (ha' : a ∘ₗ e'.toLinearMap = jetContactCovector K U)
    (hB'' : B.compl₁₂ e'.toLinearMap e'.toLinearMap = jetContactBilinForm K U) :
    ∃ S : Module.Dual K U →ₗ[K] U, (∀ p p' : Module.Dual K U, p' (S p) = p (S p')) ∧
      ∀ x, e.symm (e' x) = (x.1 + S x.2.1, x.2) := by
  -- `e⁻¹ ∘ e'` fixes the zero section and `∂_z`, and preserves the coordinates `(p, z)`.
  set S : Module.Dual K U →ₗ[K] U := LinearMap.fst K U _ ∘ₗ
    (e.symm.toLinearMap ∘ₗ e'.toLinearMap) ∘ₗ
      (LinearMap.inr K U _ ∘ₗ LinearMap.inl K (Module.Dual K U) K)
  have hsnd (x : U × Module.Dual K U × K) : (e.symm (e' x)).2 = x.2 := by
    have h1 := contactPairing_apply_eq_snd he ha hB' (e.symm (e' x))
    have h2 := contactPairing_apply_eq_snd he' ha' hB'' x
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h1 h2
    rw [← h1, h2]
  have hzero (q : U) : e.symm (e' (q, 0, 0)) = (q, 0, 0) := by
    rw [e.symm_apply_eq]
    exact (LinearMap.congr_fun he' q).trans (LinearMap.congr_fun he q).symm
  have hreeb : e.symm (e' (0, 0, 1)) = (0, 0, 1) := by
    rw [e.symm_apply_eq, h.apply_eq_reebVector hB e ha hB', h.apply_eq_reebVector hB e' ha' hB'']
  have hS (p : Module.Dual K U) : e.symm (e' (0, p, 0)) = (S p, p, 0) :=
    Prod.ext (by simp [S]) (by simpa using hsnd (0, p, 0))
  have hx (x : U × Module.Dual K U × K) : e.symm (e' x) = (x.1 + S x.2.1, x.2) := by
    obtain ⟨q, p, z⟩ := x
    have hdec : ((q, p, z) : U × Module.Dual K U × K) =
        (q, 0, 0) + (0, p, 0) + z • (0, 0, 1) := by
      simp
    calc e.symm (e' (q, p, z)) = e.symm (e' ((q, 0, 0) + (0, p, 0) + z • (0, 0, 1))) := by
          rw [← hdec]
      _ = (q + S p, p, z) := by
          simp only [map_add, map_smul, hzero, hS, hreeb]
          simp
  refine ⟨S, fun p p' ↦ ?_, hx⟩
  -- Both `e (S p, p, 0) = e' (0, p, 0)` and `e (S p', p', 0)` lie in the image of
  -- `{0} × U^* × {0}` under `e'`, on which `B` vanishes.
  have h1 : B (e' (0, p, 0)) (e' (0, p', 0)) = p' (S p) - p (S p') := by
    rw [← e.apply_symm_apply (e' (0, p, 0)), ← e.apply_symm_apply (e' (0, p', 0)), hS, hS]
    simpa using LinearMap.congr_fun₂ hB' (S p, p, 0) (S p', p', 0)
  have h0 : B (e' (0, p, 0)) (e' (0, p', 0)) = 0 := by
    simpa using LinearMap.congr_fun₂ hB'' (0, p, 0) (0, p', 0)
  exact sub_eq_zero.1 (h1.symm.trans h0)

end Module.Dual
