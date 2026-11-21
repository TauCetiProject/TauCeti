/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint
public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice
public import TauCeti.Geometry.Symplectic.Lagrangian.CoisotropicModel.Equivariant
public import TauCeti.Geometry.Symplectic.LinearReduction.Equivariant
import Mathlib.RepresentationTheory.Maschke

/-!
# The linear normal form of a Hamiltonian action at a point

Let `Z ↦ Z_M` be an infinitesimal action of a Lie algebra `𝔤` on a manifold `M` with a
nondegenerate two-form `σ`, let `μ : M → 𝔤*` and `x ∈ M`, and suppose the moment identity
`σ_x(ξ_M, ζ_M) = μ(x) ⁅ξ, ζ⁆` holds at `x`, as it does for a coadjoint-equivariant moment map. Put
`ν = μ(x)`, let `𝔥 = 𝔤_x` be the isotropy algebra and `𝔨 = 𝔤_ν` the coadjoint stabilizer, so that
`𝔥 ≤ 𝔨`, and choose complements

`𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮`, with `𝔥 ⊕ 𝔪 = 𝔨`.

The **linear normal form** of Marle and of Guillemin–Sternberg identifies the symplectic vector
space `(T_x M, σ_x)` with the model

`(𝔪 × 𝔪*) × (𝔮 × V)`, `Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + ν ⁅ζ, ζ'⁆ + ω_V(v, v')`,

where `V = W^σ ⧸ (W ∩ W^σ)` is the symplectic slice of the orbit tangent space `W = 𝔤 · x`
(`TauCeti.SmoothTwoForm.IsNondegenerate.SymplecticSlice`). The three summands are the canonical
form of the linear cotangent space `𝔪 × 𝔪*` (`TauCeti.cotangentSymplecticForm`), the Kirillov form
on `𝔮 ≅ 𝔤 ⧸ 𝔨`, which is the KKS form of the coadjoint orbit through `ν`
(`Module.Dual.kirillovSymplecticForm`), and the reduced form of the slice. It is the value at the
base point `[1, 0, 0]` of the symplectic form of the local model `G ×_H (𝔪* × V)` of a Hamiltonian
action near the orbit through `x`.

The identification `e` can be chosen to restrict to the orbit map on the orbit directions,
`e(ξ, 0, ζ, 0) = (ξ + ζ)_M(x)` for `ξ ∈ 𝔪` and `ζ ∈ 𝔮`, and to lift the slice: for `u ∈ W^σ`, the
vector `e(0, 0, 0, [u])` differs from `u` by an orbit direction
(`IsNondegenerate.exists_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice`).

The statement is linear algebra, proved for an arbitrary linear map `ρ : 𝔤 → T` into a
finite-dimensional symplectic vector space `(T, ω)` with `ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆`
(`TauCeti.SymplecticForm.exists_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`).
Then `ρ(𝔨) = W ∩ W^ω` for `W = ρ(𝔤)`, and the orbit directions together with a lift of the slice
form a coisotropic subspace on which `ω` is the restriction of the model form. No finiteness of `𝔤`
is needed, and the complements need not be invariant under any group: the statement is the case of
the trivial group of the equivariant normal form below.

**The equivariant normal form.** Let a group `H` act on `(T, ω)` by symplectomorphisms `τ` and on
`𝔤` by a representation `Ad`, with `ρ` equivariant; for the stabilizer `H = G_x` of a point these
are the tangent and adjoint representations. If `τ` is semisimple, as for a continuous
representation of a compact group, the identification `e` can be chosen `H`-equivariant, for the
action of `H` on the model by `Ad` on `𝔪` and `𝔮`, its dual on `𝔪*` and `[u] ↦ [τ h u]` on `V`,
provided `𝔪` and `𝔮` are `Ad`-invariant
(`SymplecticForm.exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`).
Invariant complements exist when `Ad` is semisimple
(`TauCeti.SymplecticForm.exists_subrepresentation_isCompl_lieAnnihilator`). The proof extends
from the coisotropic subspace `W + W^ω`, the image of `(𝔪 × 𝔮) × V` under the orbit map and an
equivariant lift of the slice (`TauCeti.SymplecticForm.exists_equivariant_section_reducedSpace`).
Its coisotropic model is the normal form model, and the equivariant coisotropic embedding theorem
(`LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel`) extends the
embedding equivariantly; only the target representation `τ` needs to be semisimple.

## Main results

* `TauCeti.SymplecticForm.exists_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`: the
  linear normal form for a linear map `ρ` satisfying the moment identity.
* `SymplecticForm.exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`:
  its equivariant version for a semisimple action by symplectomorphisms and invariant complements.
* `TauCeti.SymplecticForm.exists_subrepresentation_isCompl_lieAnnihilator`: invariant complements
  for a semisimple representation of `H` on `𝔤`.
* `IsNondegenerate.exists_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice`:
  the linear normal form of `(T_x M, σ_x)` at a point where the cocycle of `μ` vanishes.

## References

* C.-M. Marle, *Modèle d'action hamiltonienne d'un groupe de Lie sur une variété symplectique*,
  Rend. Sem. Mat. Univ. Politec. Torino 43 (1985), 227–251.
* V. Guillemin, S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics* (Jerusalem, 1982), Math. Phys. Stud. 6, Reidel, 1984, 161–175.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 7.1 (the symplectic slice and the model space).
-/

public section

open Module

namespace TauCeti

namespace SymplecticForm

variable {T : Type*} [AddCommGroup T] [Module ℝ T] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {ω : SymplecticForm T} {ρ : 𝔤 →ₗ[ℝ] T} {ν : Dual ℝ 𝔤}

/-! ### The orbit directions -/

/-- If `𝔤 = (ker ρ ⊕ 𝔪) ⊕ 𝔮`, then `ρ` maps `𝔪 × 𝔮` onto its range by `(ξ, ζ) ↦ ρ ξ + ρ ζ`. -/
private theorem range_coprod {𝔪 𝔮 : Submodule ℝ 𝔤}
    (h𝔪' : LinearMap.ker ρ ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 ν).toSubmodule)
    (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮) :
    LinearMap.range ((ρ ∘ₗ 𝔪.subtype).coprod (ρ ∘ₗ 𝔮.subtype)) = LinearMap.range ρ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨m, q⟩, rfl⟩
    exact ⟨m + q, by simp⟩
  rintro _ ⟨ξ, rfl⟩
  obtain ⟨κ, hκ, q, hq, rfl⟩ := Submodule.mem_sup.1 (h𝔮.sup_eq_top ▸ Submodule.mem_top (x := ξ))
  obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.1 (h𝔪'.symm ▸ hκ : κ ∈ LinearMap.ker ρ ⊔ 𝔪)
  exact ⟨(⟨m, hm⟩, ⟨q, hq⟩), by simp [LinearMap.mem_ker.1 hk]⟩

section Orbit

variable (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆)
include hρ

/-- Under the moment identity, `ρ ξ` is `ω`-orthogonal to every `ρ ζ` exactly when `ξ` lies in the
coadjoint stabilizer `𝔤_ν`. -/
private theorem mem_lieAnnihilator_iff (ξ : 𝔤) :
    ξ ∈ (lieAnnihilator ℝ 𝔤 ν).toSubmodule ↔ ∀ ζ, ω (ρ ξ) (ρ ζ) = 0 := by
  simp only [← ν.ker_kirillovForm, LinearMap.mem_ker, LinearMap.ext_iff,
    Dual.kirillovForm_apply, LinearMap.zero_apply, hρ]

/-- The kernel of `ρ` lies in the coadjoint stabilizer `𝔤_ν`. -/
private theorem ker_le_lieAnnihilator :
    LinearMap.ker ρ ≤ (lieAnnihilator ℝ 𝔤 ν).toSubmodule := fun ξ hξ ↦ by
  rw [mem_lieAnnihilator_iff hρ]
  intro ζ
  rw [LinearMap.mem_ker.1 hξ]
  exact LinearMap.map_zero₂ _ _

/-- The orbit directions of a complement `𝔪` of `ker ρ` in `𝔤_ν` are `ω`-orthogonal to the
orbit. -/
private theorem apply_eq_zero_of_mem {𝔪 : Submodule ℝ 𝔤}
    (h𝔪 : LinearMap.ker ρ ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 ν).toSubmodule) {m : 𝔤} (hm : m ∈ 𝔪)
    (ζ : 𝔤) : ω (ρ m) (ρ ζ) = 0 :=
  (mem_lieAnnihilator_iff hρ m).1 (h𝔪 ▸ Submodule.mem_sup_right hm) ζ

/-- On the orbit directions of a complement `𝔪` of `ker ρ` in `𝔤_ν`, the orbit directions of any
`b, b'`, and a lift `s` of the reduced space of `W^ω`, the form `ω` is the model form: the
directions of `𝔪` are `ω`-orthogonal to the orbit, and the lift is `ω`-orthogonal to the orbit. -/
private theorem apply_add_add_apply_add_add {𝔪 : Submodule ℝ 𝔤}
    (h𝔪' : LinearMap.ker ρ ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 ν).toSubmodule)
    (s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ))
    (hs : ∀ v, Submodule.Quotient.mk (s v) = v) (a a' : 𝔪) (b b' : 𝔤)
    (v v' : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :
    ω (ρ a + ρ b + s v) (ρ a' + ρ b' + s v') =
      ν ⁅b, b'⁆ + ω.reduction (ω.orthogonal (LinearMap.range ρ)) v v' := by
  have hK (m : 𝔪) (ζ : 𝔤) : ω (ρ m) (ρ ζ) = 0 := apply_eq_zero_of_mem hρ h𝔪' m.property ζ
  have hρU (ξ : 𝔤) (u : ω.orthogonal (LinearMap.range ρ)) : ω (ρ ξ) u = 0 := u.property _ ⟨ξ, rfl⟩
  have hUρ (ξ : 𝔤) (u : ω.orthogonal (LinearMap.range ρ)) : ω u (ρ ξ) = 0 :=
    ω.isRefl.eq_zero (hρU ξ u)
  have h₁ : ω (s v) (s v') = ω.reduction _ v v' := by
    conv_rhs => rw [← hs v, ← hs v', reduction_mk]
  have h₂ : ω (ρ b) (ρ a') = 0 := ω.isRefl.eq_zero (hK a' b)
  simp only [map_add, LinearMap.add_apply, hρU, hUρ, hK, h₁, h₂, hρ]
  ring

variable {𝔪 𝔮 : Submodule ℝ 𝔤} (h𝔪 : Disjoint (LinearMap.ker ρ) 𝔪)
  (h𝔪' : LinearMap.ker ρ ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 ν).toSubmodule)
  (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮)
include h𝔪 h𝔪' h𝔮

/-- If `𝔤 = (ker ρ ⊕ 𝔪) ⊕ 𝔮` with `ker ρ ⊕ 𝔪 = 𝔤_ν`, then `(ξ, ζ) ↦ ρ ξ + ρ ζ` is injective on
`𝔪 × 𝔮`. -/
private theorem injective_coprod :
    Function.Injective ((ρ ∘ₗ 𝔪.subtype).coprod (ρ ∘ₗ 𝔮.subtype)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨a, b⟩ h
  simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, ← map_add] at h
  have hab : (a : 𝔤) + b ∈ (lieAnnihilator ℝ 𝔤 ν).toSubmodule := ker_le_lieAnnihilator hρ h
  have hb' := sub_mem hab (h𝔪' ▸ Submodule.mem_sup_right a.property)
  rw [add_sub_cancel_left] at hb'
  have hb : (b : 𝔤) = 0 := Submodule.disjoint_def.1 h𝔮.disjoint _ hb' b.property
  rw [hb, add_zero] at h
  have ha : (a : 𝔤) = 0 := Submodule.disjoint_def.1 h𝔪 _ h a.property
  rw [Submodule.coe_eq_zero.1 ha, Submodule.coe_eq_zero.1 hb]
  rfl

/-- The orbit directions of `𝔪 × 𝔮` together with a lift `s` of the reduced space of `W^ω`
embed into `T`: `((a, b), v) ↦ ρ a + ρ b + s v` is injective. -/
private theorem injective_coprod_coprod [FiniteDimensional ℝ T]
    (s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ))
    (hs : ∀ v, Submodule.Quotient.mk (s v) = v) :
    Function.Injective (((ρ ∘ₗ 𝔪.subtype).coprod (ρ ∘ₗ 𝔮.subtype)).coprod
      ((ω.orthogonal (LinearMap.range ρ)).subtype ∘ₗ s)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨⟨a, b⟩, v⟩ h
  simp only [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.comp_apply,
    Submodule.subtype_apply] at h
  obtain rfl : v = 0 := by
    rw [← hs v, ReducedSpace.mk_eq_zero_iff, ω.orthogonal_orthogonal,
      eq_neg_of_add_eq_zero_right h, neg_mem_iff]
    exact ⟨a + b, map_add ρ _ _⟩
  obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := Prod.ext_iff.1 <| injective_coprod hρ h𝔪 h𝔪' h𝔮
    (a₁ := (a, b)) (a₂ := 0) (by simpa using h)
  rfl

end Orbit

variable [FiniteDimensional ℝ T] (ω ρ ν)

/-! ### The equivariant linear normal form -/

section Equivariant

variable {H : Type*} [Group H] {Ad : Representation ℝ H 𝔤} {τ : H →* T ≃ₗ[ℝ] T}

omit [FiniteDimensional ℝ T] in
variable {ω ρ} in
/-- If `τ` acts by symplectomorphisms of `ω` and `ρ` intertwines `Ad` with `τ`, then `τ` preserves
the `ω`-orthogonal `W^ω` of the orbit directions `W = ρ(𝔤)`. -/
theorem apply_mem_orthogonal_range (hτ : ∀ h, IsSymplectomorphism ω ω (τ h))
    (hρτ : ∀ h ξ, ρ (Ad h ξ) = τ h (ρ ξ)) (h : H) {u : T}
    (hu : u ∈ ω.orthogonal (LinearMap.range ρ)) : τ h u ∈ ω.orthogonal (LinearMap.range ρ) :=
  apply_mem_orthogonal (ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp τ)
    (fun g ↦ (hτ g).apply) (fun g v hv ↦ by
      obtain ⟨ξ, rfl⟩ := hv
      exact ⟨Ad g ξ, hρτ g ξ⟩) h hu

omit [FiniteDimensional ℝ T] in
variable {ω ρ ν} in
/-- **Invariant complements for the linear normal form.** If `ρ : 𝔤 → T` satisfies the moment
identity `ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆` and intertwines a semisimple representation `Ad` of `H` on `𝔤`
with an action `τ` by symplectomorphisms, then `ker ρ` and the coadjoint stabilizer `𝔤_ν` are
invariant, so there are `Ad`-invariant complements `𝔪` of `ker ρ` in `𝔤_ν` and `𝔮` of `𝔤_ν` in
`𝔤`. -/
theorem exists_subrepresentation_isCompl_lieAnnihilator [Ad.IsSemisimpleRepresentation]
    (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆) (hτ : ∀ h, IsSymplectomorphism ω ω (τ h))
    (hρτ : ∀ h ξ, ρ (Ad h ξ) = τ h (ρ ξ)) :
    ∃ 𝔪 𝔮 : Subrepresentation Ad, Disjoint (LinearMap.ker ρ) 𝔪.toSubmodule ∧
      LinearMap.ker ρ ⊔ 𝔪.toSubmodule = (lieAnnihilator ℝ 𝔤 ν).toSubmodule ∧
      IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮.toSubmodule := by
  let N : Subrepresentation Ad := ⟨LinearMap.ker ρ, fun h ξ hξ ↦ by
    rw [LinearMap.mem_ker] at hξ ⊢
    rw [hρτ, hξ, map_zero]⟩
  let K : Subrepresentation Ad := ⟨(lieAnnihilator ℝ 𝔤 ν).toSubmodule, fun h ξ hξ ↦ by
    rw [mem_lieAnnihilator_iff hρ] at hξ ⊢
    intro ζ
    rw [← Ad.self_inv_apply h ζ, hρτ, hρτ, (hτ h).apply]
    exact hξ _⟩
  obtain ⟨C, hC⟩ := exists_isCompl N
  obtain ⟨𝔮, h𝔮⟩ := exists_isCompl K
  have hC' := Subrepresentation.isCompl_toSubmodule.mpr hC
  refine ⟨C ⊓ K, 𝔮, ?_, ?_, Subrepresentation.isCompl_toSubmodule.mpr h𝔮⟩
  · rw [Subrepresentation.toSubmodule_inf]
    exact hC'.disjoint.mono_right inf_le_left
  · rw [Subrepresentation.toSubmodule_inf,
      ← sup_inf_assoc_of_le _ (ker_le_lieAnnihilator hρ), hC'.sup_eq_top, top_inf_eq]

/-! #### The orbit directions together with a lifted slice -/

section OrbitSlice

omit [FiniteDimensional ℝ T]

variable {ω ρ ν} {𝔪 𝔮 : Submodule ℝ 𝔤}
  (s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ))

variable (𝔪 𝔮) in
/-- The map `((a, b), v) ↦ ρ a + ρ b + s v` from the orbit directions of `𝔪 × 𝔮` and the slice,
lifted by `s`, to `T`. -/
private def orbitSliceMap :
    (𝔪 × 𝔮) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] T :=
  ((ρ ∘ₗ 𝔪.subtype).coprod (ρ ∘ₗ 𝔮.subtype)).coprod
    ((ω.orthogonal (LinearMap.range ρ)).subtype ∘ₗ s)

private theorem orbitSliceMap_apply (a : 𝔪) (b : 𝔮)
    (v : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :
    orbitSliceMap 𝔪 𝔮 s ((a, b), v) = ρ a + ρ b + s v := by
  simp [orbitSliceMap]

variable (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆)
  (h𝔪' : LinearMap.ker ρ ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 ν).toSubmodule)
  (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮) {s}
  (hs : ∀ v, Submodule.Quotient.mk (s v) = v)
include hρ h𝔪' hs

/-- The form `ω` pulled back along `orbitSliceMap` is `ν ⁅b, b'⁆ + ω_V(v, v')`. -/
private theorem apply_orbitSliceMap_orbitSliceMap (a a' : 𝔪) (b b' : 𝔮)
    (v v' : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :
    ω (orbitSliceMap 𝔪 𝔮 s ((a, b), v)) (orbitSliceMap 𝔪 𝔮 s ((a', b'), v')) =
      ν ⁅(b : 𝔤), b'⁆ + ω.reduction _ v v' := by
  rw [orbitSliceMap_apply, orbitSliceMap_apply]
  exact apply_add_add_apply_add_add hρ h𝔪' s hs a a' b b' v v'

include h𝔮 in
/-- The kernel of the pulled back form is `𝔪 × 0 × 0`: the Kirillov form on `𝔮` and the reduced
form on the slice are nondegenerate. -/
private theorem mem_ker_orbitSliceMap_iff
    (w : (𝔪 × 𝔮) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :
    w ∈ LinearMap.ker (ω.toBilinForm.compl₁₂ (orbitSliceMap 𝔪 𝔮 s) (orbitSliceMap 𝔪 𝔮 s)) ↔
      w.1.2 = 0 ∧ w.2 = 0 := by
  have hB := apply_orbitSliceMap_orbitSliceMap (𝔮 := 𝔮) hρ h𝔪' hs
  obtain ⟨⟨a, b⟩, v⟩ := w
  refine ⟨fun hw ↦ ⟨?_, ?_⟩, fun ⟨hb, hv⟩ ↦ ?_⟩
  · refine (ν.kirillovSymplecticForm h𝔮).separatingLeft b fun b' ↦ ?_
    simpa [hB] using LinearMap.congr_fun (LinearMap.mem_ker.1 hw) ((0, b'), 0)
  · refine (ω.reduction _).separatingLeft v fun v' ↦ ?_
    simpa [hB] using LinearMap.congr_fun (LinearMap.mem_ker.1 hw) ((0, 0), v')
  · dsimp only at hb hv
    subst hb hv
    refine LinearMap.mem_ker.2 (LinearMap.ext fun w' ↦ ?_)
    obtain ⟨⟨a', b'⟩, v'⟩ := w'
    simp [hB]

omit hρ h𝔪' in
/-- The lift `s [u]` differs from `u` by an orbit direction. -/
private theorem coe_apply_mk_sub_mem_range [FiniteDimensional ℝ T]
    (u : ω.orthogonal (LinearMap.range ρ)) :
    (s (Submodule.Quotient.mk u) : T) - u ∈ LinearMap.range ρ := by
  have hu := ReducedSpace.mk_eq_mk_iff.1 (hs (Submodule.Quotient.mk u))
  rwa [ω.orthogonal_orthogonal] at hu

omit hρ in
include h𝔮 in
/-- The image `W + W^ω` of `orbitSliceMap` is coisotropic. -/
private theorem isCoisotropic_range_orbitSliceMap [FiniteDimensional ℝ T] :
    ω.IsCoisotropic (LinearMap.range (orbitSliceMap 𝔪 𝔮 s)) := by
  have hrange : LinearMap.range ρ ≤ LinearMap.range (orbitSliceMap 𝔪 𝔮 s) := by
    refine (range_coprod h𝔪' h𝔮).ge.trans ?_
    rintro _ ⟨⟨a, b⟩, rfl⟩
    exact ⟨((a, b), 0), by simp [orbitSliceMap_apply]⟩
  have hU : ω.orthogonal (LinearMap.range ρ) ≤ LinearMap.range (orbitSliceMap 𝔪 𝔮 s) :=
    fun u hu ↦ by
      obtain ⟨w, hw⟩ := hrange (coe_apply_mk_sub_mem_range hs ⟨u, hu⟩)
      refine ⟨((0, 0), Submodule.Quotient.mk ⟨u, hu⟩) - w, ?_⟩
      rw [map_sub, hw, orbitSliceMap_apply]
      simp
  exact isCoisotropic_iff.2 fun _ hv ↦
    hrange ((ω.orthogonal_orthogonal (LinearMap.range ρ)).le (ω.orthogonal_le hU hv))

include h𝔮 in
/-- The kernel of the pulled back form is identified with `𝔪` by `a ↦ ((a, 0), 0)`. -/
private theorem exists_linearEquiv_ker_orbitSliceMap :
    ∃ j : 𝔪 ≃ₗ[ℝ]
        LinearMap.ker (ω.toBilinForm.compl₁₂ (orbitSliceMap 𝔪 𝔮 s) (orbitSliceMap 𝔪 𝔮 s)),
      ∀ a, (j a : (𝔪 × 𝔮) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) = ((a, 0), 0) := by
  have hker := mem_ker_orbitSliceMap_iff hρ h𝔪' h𝔮 hs
  refine ⟨LinearEquiv.ofBijective (LinearMap.codRestrict _
    (LinearMap.inl ℝ _ _ ∘ₗ LinearMap.inl ℝ _ _) fun a ↦ (hker _).2 ⟨rfl, rfl⟩)
    ⟨fun a a' h ↦ congrArg (fun k : LinearMap.ker _ ↦ k.val.1.1) h, fun k ↦ ⟨k.val.1.1, ?_⟩⟩,
    fun _ ↦ rfl⟩
  obtain ⟨hb, hv⟩ := (hker k).1 k.property
  exact Subtype.ext (Prod.ext (Prod.ext rfl hb.symm) hv.symm)

end OrbitSlice

/-- The rearrangement `((a, α), (b, v)) ↦ (((a, b), v), α ∘ j⁻¹)` of the linear normal form model
into a coisotropic model, for an identification `j` of `M` with the kernel `K`. -/
private def modelEquiv {M K Q V : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup K]
    [Module ℝ K] [AddCommGroup Q] [Module ℝ Q] [AddCommGroup V] [Module ℝ V] (j : M ≃ₗ[ℝ] K) :
    ((M × Dual ℝ M) × (Q × V)) ≃ₗ[ℝ] ((M × Q) × V) × Dual ℝ K where
  toFun x := (((x.1.1, x.2.1), x.2.2), j.symm.dualMap x.1.2)
  invFun y := ((y.1.1.1, j.symm.dualMap.symm y.2), (y.1.1.2, y.1.2))
  map_add' _ _ := by simp
  map_smul' _ _ := by simp
  left_inv _ := by
    dsimp only
    rw [LinearEquiv.symm_apply_apply]
  right_inv _ := by
    dsimp only
    rw [LinearEquiv.apply_symm_apply]

section ModelEquiv

variable {M Q V : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup Q] [Module ℝ Q]
  [AddCommGroup V] [Module ℝ V] {B : LinearMap.BilinForm ℝ ((M × Q) × V)}
  (j : M ≃ₗ[ℝ] LinearMap.ker B)

omit [FiniteDimensional ℝ T]

private theorem modelEquiv_apply (a : M) (α : Dual ℝ M) (b : Q) (v : V) :
    modelEquiv j ((a, α), (b, v)) = (((a, b), v), j.symm.dualMap α) :=
  rfl

/-- If `B((a, b), v)((a', b'), v') = κ(b, b') + β(v, v')` and the projection `P` onto the kernel of
`B` reads off the first coordinate through `j`, then `modelEquiv j` is a symplectomorphism from the
linear normal form model onto the coisotropic model of `B`. -/
private theorem isSymplectomorphism_modelEquiv (hB : B.IsAlt) {κ : SymplecticForm Q}
    {β : SymplecticForm V}
    (hBκβ : ∀ a a' b b' v v', B ((a, b), v) ((a', b'), v') = κ b b' + β v v')
    {P : (M × Q) × V →ₗ[ℝ] LinearMap.ker B} (hP : ∀ k : LinearMap.ker B, P k = k)
    (hPj : ∀ w, P w = j w.1.1) :
    IsSymplectomorphism (cotangentSymplecticForm.prod (κ.prod β)) (hB.coisotropicModel P hP)
      (modelEquiv j) :=
  isSymplectomorphism_iff.2 fun ⟨⟨a, α⟩, b, v⟩ ⟨⟨a', α'⟩, b', v'⟩ ↦ by
    simp only [modelEquiv_apply, LinearMap.BilinForm.IsAlt.coisotropicModel_apply, hBκβ, hPj,
      LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply, prod_apply,
      cotangentSymplecticForm_apply]
    ring

/-- If `j` intertwines a representation `σM` with the restriction to the kernel of an invariant
form `B`, then `modelEquiv j` intertwines the linear normal form model with the coisotropic model
of `B`. -/
private theorem modelEquiv_apply_prod {H : Type*} [Group H] {σM : Representation ℝ H M}
    {σQ : Representation ℝ H Q} {σV : Representation ℝ H V}
    (hσ : Representation.IsInvariantForm ((σM.prod σQ).prod σV) B)
    (hjσ : ∀ g a, j (σM g a) = hσ.kerRepresentation g (j a)) (g : H)
    (x : (M × Dual ℝ M) × (Q × V)) :
    modelEquiv j (((σM.prod σM.dual).prod (σQ.prod σV)) g x) =
      (((σM.prod σQ).prod σV).prod hσ.kerRepresentation.dual) g (modelEquiv j x) := by
  have hjσ' (g : H) (k : LinearMap.ker B) :
      j.symm (hσ.kerRepresentation g k) = σM g (j.symm k) := by
    rw [LinearEquiv.symm_apply_eq, hjσ, LinearEquiv.apply_symm_apply]
  obtain ⟨⟨a, α⟩, b, v⟩ := x
  simp only [Representation.prod_apply_apply, modelEquiv_apply]
  refine Prod.ext rfl ?_
  ext k
  simp only [Representation.dual_apply, Dual.transpose_apply, LinearEquiv.dualMap_apply,
    LinearMap.comp_apply, hjσ']

end ModelEquiv

omit [FiniteDimensional ℝ T] in
variable {ω ρ} in
/-- With an equivariant lift `s`, `orbitSliceMap` intertwines `Ad` on `𝔪 × 𝔮` and the action on the
slice with `τ`. -/
private theorem orbitSliceMap_apply_prod (hτ : ∀ h, IsSymplectomorphism ω ω (τ h))
    (hρτ : ∀ h ξ, ρ (Ad h ξ) = τ h (ρ ξ)) {𝔪 𝔮 : Subrepresentation Ad}
    {s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ)}
    (hsτ : ∀ h v, (s (ω.reducedSpaceRepresentation τ hτ _
      (fun h _ ↦ apply_mem_orthogonal_range hτ hρτ h) h v) : T) = τ h (s v)) (h : H)
    (w : (𝔪.toSubmodule × 𝔮.toSubmodule) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :
    orbitSliceMap 𝔪.toSubmodule 𝔮.toSubmodule s
        (((𝔪.toRepresentation.prod 𝔮.toRepresentation).prod
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (ω.reducedSpaceRepresentation τ
            hτ _ fun h _ ↦ apply_mem_orthogonal_range hτ hρτ h))) h w) =
      τ h (orbitSliceMap 𝔪.toSubmodule 𝔮.toSubmodule s w) := by
  obtain ⟨⟨a, b⟩, v⟩ := w
  simp only [Representation.prod_apply_apply, orbitSliceMap_apply,
    Subrepresentation.coe_toRepresentation_apply, hρτ,
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom_comp_apply, map_add, hsτ]

variable [Representation.IsSemisimpleRepresentation
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp τ : Representation ℝ H T)]

/-- **The equivariant linear normal form.** Let a group `H` act on a finite-dimensional symplectic
vector space `(T, ω)` by a semisimple representation `τ` by symplectomorphisms, and on a Lie algebra
`𝔤` by a representation `Ad`. Let `ρ : 𝔤 → T` be an `H`-equivariant linear map with
`ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆`, and choose `Ad`-invariant complements `𝔪` of `ker ρ` in the coadjoint
stabilizer `𝔤_ν` and `𝔮` of `𝔤_ν` in `𝔤`. Then some linear symplectomorphism from

`(𝔪 × 𝔪*) × (𝔮 × V)`, `V = W^ω ⧸ (W ∩ W^ω)` for `W = ρ(𝔤)`,

to `(T, ω)` with the properties of
`exists_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction` is `H`-equivariant, where `H`
acts on `𝔪` and `𝔮` by `Ad`, on `𝔪*` by the dual of `Ad`, and on `V` by `[u] ↦ [τ h u]`. -/
theorem exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction
    (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆) (hτ : ∀ h, IsSymplectomorphism ω ω (τ h))
    (hρτ : ∀ h ξ, ρ (Ad h ξ) = τ h (ρ ξ)) {𝔪 𝔮 : Subrepresentation Ad}
    (h𝔪 : Disjoint (LinearMap.ker ρ) 𝔪.toSubmodule)
    (h𝔪' : LinearMap.ker ρ ⊔ 𝔪.toSubmodule = (lieAnnihilator ℝ 𝔤 ν).toSubmodule)
    (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮.toSubmodule) :
    ∃ e : ((𝔪.toSubmodule × Dual ℝ 𝔪.toSubmodule) ×
        (𝔮.toSubmodule × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))) ≃ₗ[ℝ] T,
      IsSymplectomorphism (cotangentSymplecticForm.prod ((ν.kirillovSymplecticForm h𝔮).prod
        (ω.reduction (ω.orthogonal (LinearMap.range ρ))))) ω e ∧
      (∀ ξ : 𝔪.toSubmodule, e ((ξ, 0), (0, 0)) = ρ ξ) ∧
      (∀ ζ : 𝔮.toSubmodule, e ((0, 0), (ζ, 0)) = ρ ζ) ∧
      (∀ u : ω.orthogonal (LinearMap.range ρ),
        e ((0, 0), (0, Submodule.Quotient.mk u)) - u ∈ LinearMap.range ρ) ∧
      ∀ h x, e (((𝔪.toRepresentation.prod 𝔪.toRepresentation.dual).prod
        (𝔮.toRepresentation.prod (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
          (ω.reducedSpaceRepresentation τ hτ _
            fun h _ ↦ apply_mem_orthogonal_range hτ hρτ h)))) h x) = τ h (e x) := by
  have hU : ∀ h, ∀ u ∈ ω.orthogonal (LinearMap.range ρ), τ h u ∈ ω.orthogonal (LinearMap.range ρ) :=
    fun h _ ↦ apply_mem_orthogonal_range hτ hρτ h
  obtain ⟨s, hs, hsτ⟩ := exists_equivariant_section_reducedSpace hτ _ hU
  -- `H` acts on the source `(𝔪 × 𝔮) × V` of the equivariant embedding `F` into `T`.
  let σ := (𝔪.toRepresentation.prod 𝔮.toRepresentation).prod
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (ω.reducedSpaceRepresentation τ hτ _ hU))
  let F := orbitSliceMap 𝔪.toSubmodule 𝔮.toSubmodule s
  -- The pulled back form `B` has kernel `𝔪 × 0 × 0`, with an equivariant projection `P`.
  let B : LinearMap.BilinForm ℝ
      ((𝔪.toSubmodule × 𝔮.toSubmodule) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :=
    ω.toBilinForm.compl₁₂ F F
  have hB : B.IsAlt := fun w ↦ ω.self_eq_zero (F w)
  obtain ⟨j, hj⟩ := exists_linearEquiv_ker_orbitSliceMap (s := s) hρ h𝔪' h𝔮 hs
  let P : (𝔪.toSubmodule × 𝔮.toSubmodule) × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ]
      LinearMap.ker B := j.toLinearMap ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ LinearMap.fst ℝ _ _
  have hP (k : LinearMap.ker B) : P k = k := by
    obtain ⟨hb, hv⟩ := (mem_ker_orbitSliceMap_iff hρ h𝔪' h𝔮 hs k).1 k.property
    exact Subtype.ext ((hj _).trans (Prod.ext (Prod.ext rfl hb.symm) hv.symm))
  have hσB : Representation.IsInvariantForm σ B := Representation.isInvariantForm_iff.2
    fun h w w' ↦ by
      simp only [B, LinearMap.compl₁₂_apply, F, σ, orbitSliceMap_apply_prod hτ hρτ hsτ]
      exact (hτ h).apply _ _
  -- `F` extends to an equivariant symplectomorphism from the coisotropic model of `B`, which is
  -- the linear normal form model through `modelEquiv j`.
  obtain ⟨e₂, he₂, he₂F, he₂σ⟩ := hB.exists_equivariant_isSymplectomorphism_coisotropicModel
    (ρ := LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp τ) (ι := F) hP
    (Representation.isInvariantForm_iff.2 fun h u v ↦ (hτ h).apply u v) hσB
    (injective_coprod_coprod hρ h𝔪 h𝔪' h𝔮 s hs)
    (fun w w' ↦ (LinearMap.compl₁₂_apply ω.toBilinForm F F w w').symm)
    (isCoisotropic_range_orbitSliceMap h𝔪' h𝔮 hs) (orbitSliceMap_apply_prod hτ hρτ hsτ)
    fun h w ↦ by simp [P, hj, σ]
  refine ⟨(modelEquiv j).trans e₂, (isSymplectomorphism_modelEquiv j hB
    (fun a a' b b' v v' ↦ ?_) hP fun _ ↦ rfl).trans he₂, fun ξ ↦ ?_, fun ζ ↦ ?_, fun u ↦ ?_,
    fun h x ↦ ?_⟩
  · rw [Dual.kirillovSymplecticForm_apply]
    exact apply_orbitSliceMap_orbitSliceMap hρ h𝔪' hs a a' b b' v v'
  · rw [LinearEquiv.trans_apply, modelEquiv_apply, map_zero, he₂F, orbitSliceMap_apply]
    simp
  · rw [LinearEquiv.trans_apply, modelEquiv_apply, map_zero, he₂F, orbitSliceMap_apply]
    simp
  · rw [LinearEquiv.trans_apply, modelEquiv_apply, map_zero, he₂F, orbitSliceMap_apply]
    simpa using coe_apply_mk_sub_mem_range hs u
  · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      modelEquiv_apply_prod j hσB (fun g a ↦ Subtype.ext (by simp [hj, σ])), he₂σ]
    exact LinearEquiv.automorphismGroup.toLinearMapMonoidHom_comp_apply τ h _

end Equivariant

/-! ### The linear normal form -/

/-- **The linear normal form of Marle and Guillemin–Sternberg.** Let `ρ : 𝔤 → T` be a linear map
into a finite-dimensional symplectic vector space `(T, ω)` with `ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆`, let `𝔪`
be a complement of `ker ρ` in the coadjoint stabilizer `𝔤_ν`, and `𝔮` a complement of `𝔤_ν` in
`𝔤`. Write `W = ρ(𝔤)` and `V = W^ω ⧸ (W ∩ W^ω)` for the reduced space of `W^ω`. Then some linear
symplectomorphism from

`(𝔪 × 𝔪*) × (𝔮 × V)`, `Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + ν ⁅ζ, ζ'⁆ + ω_V(v, v')`

to `(T, ω)` sends `(ξ, 0, 0, 0)` to `ρ ξ` and `(0, 0, ζ, 0)` to `ρ ζ`, and sends `(0, 0, 0, [u])`,
for `u ∈ W^ω`, to `u` plus an element of `W`. This is the case of the trivial group of
`exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`. -/
theorem exists_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction
    (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆) {𝔪 𝔮 : Submodule ℝ 𝔤}
    (h𝔪 : Disjoint (LinearMap.ker ρ) 𝔪)
    (h𝔪' : LinearMap.ker ρ ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 ν).toSubmodule)
    (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮) :
    ∃ e : ((𝔪 × Dual ℝ 𝔪) × (𝔮 × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))) ≃ₗ[ℝ] T,
      IsSymplectomorphism (cotangentSymplecticForm.prod ((ν.kirillovSymplecticForm h𝔮).prod
        (ω.reduction (ω.orthogonal (LinearMap.range ρ))))) ω e ∧
      (∀ ξ : 𝔪, e ((ξ, 0), (0, 0)) = ρ ξ) ∧ (∀ ζ : 𝔮, e ((0, 0), (ζ, 0)) = ρ ζ) ∧
      ∀ u : ω.orthogonal (LinearMap.range ρ),
        e ((0, 0), (0, Submodule.Quotient.mk u)) - u ∈ LinearMap.range ρ := by
  -- The case of the trivial group, with `𝔪` and `𝔮` as subrepresentations of its trivial action.
  have : NeZero (Nat.card Unit : ℝ) := ⟨by simp⟩
  obtain ⟨e, he, h₁, h₂, h₃, -⟩ :=
    exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction (H := Unit)
      (Ad := 1) (τ := 1) ω ρ ν hρ (fun _ ↦ isSymplectomorphism_iff.2 fun _ _ ↦ by simp)
      (fun _ _ ↦ by simp) (𝔪 := ⟨𝔪, fun _ _ h ↦ by simpa using h⟩)
      (𝔮 := ⟨𝔮, fun _ _ h ↦ by simpa using h⟩) h𝔪 h𝔪' h𝔮
  exact ⟨e, he, h₁, h₂, h₃⟩

end SymplecticForm

/-! ### The linear normal form at a point of a manifold -/

open scoped ContDiff

namespace SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Dual ℝ 𝔤} {x : M}

/-- **The linear normal form of a Hamiltonian action at a point.** Let `σ` be a nondegenerate
two-form on a finite-dimensional manifold, carrying an infinitesimal action `Z ↦ Z_M` of `𝔤`, and
let `μ : M → 𝔤*` have vanishing cocycle at `x`, so that `σ_x(ξ_M, ζ_M) = μ(x) ⁅ξ, ζ⁆`. Let `𝔪` be a
complement of the isotropy algebra `𝔤_x` in the coadjoint stabilizer `𝔤_{μ(x)}`, and `𝔮` a
complement of `𝔤_{μ(x)}` in `𝔤`. Then some linear symplectomorphism from

`(𝔪 × 𝔪*) × (𝔮 × V)`, `Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + μ(x) ⁅ζ, ζ'⁆ +
ω_V(v, v')`,

where `V` is the symplectic slice at `x`, to `(T_x M, σ_x)` sends `(ξ, 0, 0, 0)` to `ξ_M(x)`,
`(0, 0, ζ, 0)` to `ζ_M(x)`, and `(0, 0, 0, [u])` to `u` plus an orbit direction. -/
theorem exists_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice
    [FiniteDimensional ℝ E] (hσ : σ.IsNondegenerate) (hc : σ.momentCocycle a μ x = 0)
    {𝔪 𝔮 : Submodule ℝ 𝔤} (h𝔪 : Disjoint (a.isotropy x).toSubmodule 𝔪)
    (h𝔪' : (a.isotropy x).toSubmodule ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule)
    (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 (μ x)).toSubmodule 𝔮) :
    ∃ e : ((𝔪 × Dual ℝ 𝔪) × (𝔮 × hσ.SymplecticSlice a x)) ≃ₗ[ℝ] TangentSpace I x,
      SymplecticForm.IsSymplectomorphism (cotangentSymplecticForm.prod
        (((μ x).kirillovSymplecticForm h𝔮).prod ((hσ.symplecticFormAt x).reduction
          ((hσ.symplecticFormAt x).orthogonal (a.orbitTangent x))))) (hσ.symplecticFormAt x) e ∧
      (∀ ξ : 𝔪, e ((ξ, 0), (0, 0)) = a ξ x) ∧ (∀ ζ : 𝔮, e ((0, 0), (ζ, 0)) = a ζ x) ∧
      ∀ u : (hσ.symplecticFormAt x).orthogonal (a.orbitTangent x),
        e ((0, 0), (0, Submodule.Quotient.mk u)) - u ∈ a.orbitTangent x := by
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [InfinitesimalAction.isotropy_toSubmodule] at h𝔪 h𝔪'
  -- `a.orbitTangent x` occurs in the types of `e` and `u` (the slice quotient and the subtype of
  -- its `σ_x`-orthogonal), so a plain `rw` with `orbitTangent_eq_range` fails on the motive; we
  -- replace it by `range (a.eval x)` everywhere at once with `generalize` and `subst`.
  unfold IsNondegenerate.SymplecticSlice
  generalize hW : a.orbitTangent x = W
  rw [InfinitesimalAction.orbitTangent_eq_range] at hW
  subst hW
  obtain ⟨e, he, h₁, h₂, h₃⟩ :=
    (hσ.symplecticFormAt x).exists_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction
      (a.eval x) (μ x) (fun ξ ζ ↦ by
        rw [symplecticFormAt_apply, InfinitesimalAction.eval_apply, InfinitesimalAction.eval_apply]
        exact momentCocycle_eq_zero_iff.1 hc ξ ζ) h𝔪 h𝔪' h𝔮
  exact ⟨e, he, fun ξ ↦ (h₁ ξ).trans (a.eval_apply x _), fun ζ ↦ (h₂ ζ).trans (a.eval_apply x _),
    h₃⟩

end SmoothTwoForm.IsNondegenerate

end TauCeti
