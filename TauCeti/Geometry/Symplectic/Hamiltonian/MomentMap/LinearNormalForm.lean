/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Symplectic.Coadjoint
public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice
public import TauCeti.Geometry.Symplectic.Lagrangian.CoisotropicModel.Equivariant

import Mathlib.RepresentationTheory.Maschke
import TauCeti.Geometry.Manifold.GroupAction.EquivariantSlice
import TauCeti.Order.ModularLattice
import TauCeti.RepresentationTheory.Continuous.Basic
import TauCeti.RepresentationTheory.Semisimple

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
No finiteness of `𝔤` is needed.

## Equivariance

When a group `K` acts on `(T, ω)` by a semisimple representation preserving `ω`, and on `𝔤` so
that `ρ` is equivariant, and `𝔪`, `𝔮` are invariant, the identification can be chosen
`K`-equivariant, for the action of `K` on the model by its actions on `𝔪` and `𝔮`, the dual
action on `𝔪*` and the induced action on `V`
(`SymplecticForm.exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`).
The orbit directions together with an equivariant lift of the slice, obtained from an equivariant
projection onto the radical of `W^ω`
(`TauCeti.SymplecticForm.exists_equivariant_lift_reducedSpace`), form an equivariant embedding of
`(𝔪 × 𝔮) × V` into `T` with coisotropic image `W + W^ω`, on which `ω` is the restriction of the
model form. Its image in the model, `(𝔪 × 0) × (𝔮 × V)`, is coisotropic as well, so the
equivariant Witt extension from coisotropic subspaces
(`TauCeti.SymplecticForm.exists_equivariant_isSymplectomorphism_extend_of_isCoisotropic`) extends
one to the other. The non-equivariant normal form is the case of the trivial group.

At a point `x` whose stabilizer `H = G_x` under a smooth action of a Lie group `G` is compact and
preserves `σ`, this applies to the tangent representation `h ↦ dh_x` of `H`, which is
semisimple by compactness. The algebras `𝔥` and `𝔨` are invariant under the adjoint action of `H`,
so they have `H`-invariant complements `𝔪` and `𝔮`
(`TauCeti.SmoothTwoForm.IsNondegenerate.exists_subrepresentation_complements`, from the algebraic
`TauCeti.SymplecticForm.exists_subrepresentation_isCompl_lieAnnihilator`), and for any such
complements the linear normal form at `x` can be chosen `H`-equivariant
(`exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice`, in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). This identifies the tangent representation
of `H` at `x` with that of the local model `G ×_H (𝔪* × V)` at `[1, 0, 0]`.

## Main results

* `TauCeti.SymplecticForm.exists_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`: the
  linear normal form for a linear map `ρ` satisfying the moment identity.
* `SymplecticForm.exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`:
  its equivariant version for a semisimple representation.
* `SymplecticForm.exists_subrepresentation_isCompl_lieAnnihilator`: invariant complements `𝔪`, `𝔮`
  for a semisimple representation on `𝔤`.
* `IsNondegenerate.exists_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice`:
  the linear normal form of `(T_x M, σ_x)` at a point where the cocycle of `μ` vanishes.
* `IsNondegenerate.exists_subrepresentation_complements`: invariant complements `𝔪`, `𝔮` for a
  compact stabilizer.
* `exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice`: the
  linear normal form at a point with compact stabilizer, equivariant for the stabilizer.

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
embed into `T`: `(a, (b, v)) ↦ ρ a + ρ b + s v` is injective. -/
private theorem injective_coprod_coprod [FiniteDimensional ℝ T]
    (s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ))
    (hs : ∀ v, Submodule.Quotient.mk (s v) = v) :
    Function.Injective ((ρ ∘ₗ 𝔪.subtype).coprod
      ((ρ ∘ₗ 𝔮.subtype).coprod ((ω.orthogonal (LinearMap.range ρ)).subtype ∘ₗ s))) := by
  have h := injective_coprod_subtype_comp (injective_coprod hρ h𝔪 h𝔪' h𝔮)
    (range_coprod h𝔪' h𝔮).le hs
  convert h.comp (LinearEquiv.prodAssoc ℝ 𝔪 𝔮 _).symm.injective using 1
  ext ⟨a, b, v⟩
  have hv : (LinearEquiv.prodAssoc ℝ 𝔪 𝔮 _).symm (a, b, v) = ((a, b), v) :=
    (LinearEquiv.symm_apply_eq _).2 (by simp)
  simp [hv, add_assoc]

/-- The model `(𝔪 × 𝔪*) × (𝔮 × V)` is finite-dimensional, since `𝔪 × (𝔮 × V)` embeds into `T`. -/
private theorem finiteDimensional_model [FiniteDimensional ℝ T]
    (s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ))
    (hs : ∀ v, Submodule.Quotient.mk (s v) = v) :
    FiniteDimensional ℝ
      ((𝔪 × Dual ℝ 𝔪) × (𝔮 × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))) := by
  have : FiniteDimensional ℝ (𝔪 × (𝔮 × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))) :=
    Module.Finite.of_injective _ (injective_coprod_coprod hρ h𝔪 h𝔪' h𝔮 s hs)
  have : FiniteDimensional ℝ 𝔪 := Module.Finite.of_injective
    (LinearMap.inl ℝ _ (𝔮 × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))))
    LinearMap.inl_injective
  have : FiniteDimensional ℝ (𝔮 × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :=
    Module.Finite.of_injective (LinearMap.inr ℝ 𝔪 _) LinearMap.inr_injective
  infer_instance

omit hρ h𝔪 in
/-- The orbit directions together with a lift `s` of the slice span the coisotropic subspace
`W + W^ω`: a vector `ω`-orthogonal to them lies in `W^ω` and is orthogonal to the lifted slice, so
its class in the slice vanishes and it lies in `(W^ω)^ω = W`. -/
private theorem isCoisotropic_range_coprod_coprod [FiniteDimensional ℝ T]
    (s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ))
    (hs : ∀ v, Submodule.Quotient.mk (s v) = v) :
    ω.IsCoisotropic (LinearMap.range ((ρ ∘ₗ 𝔪.subtype).coprod
      ((ρ ∘ₗ 𝔮.subtype).coprod ((ω.orthogonal (LinearMap.range ρ)).subtype ∘ₗ s)))) := by
  rw [LinearMap.range_coprod, LinearMap.range_coprod, ← sup_assoc, ← LinearMap.range_coprod,
    range_coprod h𝔪' h𝔮]
  exact isCoisotropic_sup_range_subtype_comp hs

end Orbit

/-! ### The equivariant linear normal form -/

section Equivariant

variable {K : Type*} [Group K] {πT : Representation ℝ K T}

section Model

variable {π𝔤 : Representation ℝ K 𝔤} (hπT : Representation.IsInvariantForm πT ω.toBilinForm)
  (hρπ : ∀ k ξ, ρ (π𝔤 k ξ) = πT k (ρ ξ))
include hπT hρπ

/-- Under the moment identity, an equivariant `ρ` makes the Kirillov form `ν ⁅ξ, ζ⁆` invariant. -/
private theorem apply_lie_apply (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆) (k : K) (ξ ζ : 𝔤) :
    ν ⁅π𝔤 k ξ, π𝔤 k ζ⁆ = ν ⁅ξ, ζ⁆ := by
  rw [← hρ, ← hρ, hρπ, hρπ]
  exact hπT.apply k _ _

/-- Under the moment identity, an equivariant `ρ` makes the coadjoint stabilizer `𝔤_ν` invariant. -/
private theorem apply_mem_lieAnnihilator (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆) (k : K) {ξ : 𝔤}
    (hξ : ξ ∈ (lieAnnihilator ℝ 𝔤 ν).toSubmodule) :
    π𝔤 k ξ ∈ (lieAnnihilator ℝ 𝔤 ν).toSubmodule := by
  rw [mem_lieAnnihilator_iff hρ] at hξ ⊢
  intro ζ
  rw [← π𝔤.self_inv_apply k ζ, hρπ, hρπ]
  exact (hπT.apply k _ _).trans (hξ _)

/-- **Invariant complements for the linear normal form.** If `ρ : 𝔤 → T` satisfies the moment
identity `ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆` and intertwines a semisimple representation `π𝔤` of `K` with a
representation `πT` preserving `ω`, then `ker ρ` and the coadjoint stabilizer `𝔤_ν` are invariant,
so there are `π𝔤`-invariant complements `𝔪` of `ker ρ` in `𝔤_ν` and `𝔮` of `𝔤_ν` in `𝔤`. -/
theorem exists_subrepresentation_isCompl_lieAnnihilator [π𝔤.IsSemisimpleRepresentation]
    (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆) :
    ∃ 𝔪 𝔮 : Subrepresentation π𝔤, Disjoint (LinearMap.ker ρ) 𝔪.toSubmodule ∧
      LinearMap.ker ρ ⊔ 𝔪.toSubmodule = (lieAnnihilator ℝ 𝔤 ν).toSubmodule ∧
      IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮.toSubmodule := by
  let N : Subrepresentation π𝔤 := ⟨LinearMap.ker ρ, fun k ξ hξ ↦ by
    rw [LinearMap.mem_ker] at hξ ⊢
    rw [hρπ, hξ, map_zero]⟩
  let A : Subrepresentation π𝔤 :=
    ⟨(lieAnnihilator ℝ 𝔤 ν).toSubmodule, fun k _ hξ ↦ apply_mem_lieAnnihilator hπT hρπ hρ k hξ⟩
  have hNA : N ≤ A := Subrepresentation.toSubmodule_le_toSubmodule.1 (ker_le_lieAnnihilator hρ)
  obtain ⟨𝔪, 𝔮, h𝔪', h𝔮, h𝔪𝔮, -⟩ := exists_sup_eq_and_isCompl_of_le hNA
  have h0 := congrArg Subrepresentation.toSubmodule
    (disjoint_iff.1 (h𝔪𝔮.disjoint.mono_right le_sup_left))
  rw [Subrepresentation.toSubmodule_inf, Subrepresentation.toSubmodule_bot] at h0
  exact ⟨𝔪, 𝔮, disjoint_iff.2 h0, congrArg Subrepresentation.toSubmodule h𝔪',
    Subrepresentation.isCompl_toSubmodule.2 h𝔮⟩

/-- The model representation on `(𝔪 × 𝔪*) × (𝔮 × V)` preserves the model form. -/
private theorem isInvariantForm_model (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆)
    {𝔪 𝔮 : Subrepresentation π𝔤} (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮.toSubmodule)
    {πV : Representation ℝ K (ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))}
    (hπV : ∀ k (u u' : ω.orthogonal (LinearMap.range ρ)), (u' : T) = πT k u →
      πV k (Submodule.Quotient.mk u) = Submodule.Quotient.mk u') :
    Representation.IsInvariantForm ((𝔪.toRepresentation.prod 𝔪.toRepresentation.dual).prod
      (𝔮.toRepresentation.prod πV)) (cotangentSymplecticForm.prod
        ((ν.kirillovSymplecticForm h𝔮).prod
          (ω.reduction (ω.orthogonal (LinearMap.range ρ))))).toBilinForm := by
  have hV := isInvariantForm_reduction (fun k u v ↦ hπT.apply k u v)
    (fun k _ hu ↦ apply_mem_orthogonal_range (fun k u v ↦ hπT.apply k u v) hρπ k hu) hπV
  refine Representation.isInvariantForm_iff.2 fun k ⟨⟨ξ, a⟩, ζ, v⟩ ⟨⟨ξ', a'⟩, ζ', v'⟩ ↦ ?_
  simp [prod_apply, hV.apply k v v', Module.Dual.transpose_apply, Representation.inv_self_apply,
    apply_lie_apply hπT hρπ hρ]

omit hπT in
/-- The model representation on `(𝔪 × 𝔪*) × (𝔮 × V)` is semisimple when `πT` is: `𝔪`, `𝔮` and `V`
embed equivariantly into `T` by `ρ` and an equivariant lift `s` of `V`, and `𝔪*` is the dual of the
finite-dimensional semisimple `𝔪`. -/
private theorem isSemisimpleRepresentation_model [FiniteDimensional ℝ T]
    [πT.IsSemisimpleRepresentation] (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆)
    {𝔪 𝔮 : Subrepresentation π𝔤} (h𝔪 : Disjoint (LinearMap.ker ρ) 𝔪.toSubmodule)
    (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮.toSubmodule)
    {πV : Representation ℝ K (ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))}
    (s : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)) →ₗ[ℝ] ω.orthogonal (LinearMap.range ρ))
    (hs : ∀ v, Submodule.Quotient.mk (s v) = v) (hsπ : ∀ k v, (s (πV k v) : T) = πT k (s v)) :
    ((𝔪.toRepresentation.prod 𝔪.toRepresentation.dual).prod
      (𝔮.toRepresentation.prod πV)).IsSemisimpleRepresentation := by
  have hinj {S : Subrepresentation π𝔤} (hS : Disjoint (LinearMap.ker ρ) S.toSubmodule) :
      Function.Injective (ρ ∘ₗ S.toSubmodule.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    exact fun ξ hξ ↦ Subtype.ext (Submodule.disjoint_def.1 hS _ hξ ξ.property)
  have hsub {S : Subrepresentation π𝔤} (hS : Disjoint (LinearMap.ker ρ) S.toSubmodule) :
      S.toRepresentation.IsSemisimpleRepresentation :=
    ((ρ ∘ₗ S.toSubmodule.subtype).intertwiningMap_of_isIntertwiningMap _ πT fun k ξ ↦
      hρπ k ξ).isSemisimpleRepresentation_of_injective (hinj hS)
  have := hsub h𝔪
  have := hsub (h𝔮.disjoint.mono_left (ker_le_lieAnnihilator hρ))
  have : πV.IsSemisimpleRepresentation :=
    (((ω.orthogonal (LinearMap.range ρ)).subtype ∘ₗ s).intertwiningMap_of_isIntertwiningMap πV πT
      hsπ).isSemisimpleRepresentation_of_injective
      ((Submodule.injective_subtype _).comp (Function.LeftInverse.injective hs))
  have : FiniteDimensional ℝ 𝔪.toSubmodule := .of_injective _ (hinj h𝔪)
  infer_instance

end Model

variable [FiniteDimensional ℝ T] (ω ρ ν)

/-- **The equivariant linear normal form.** Let a group `K` act on a finite-dimensional symplectic
vector space `(T, ω)` by a semisimple representation `πT` preserving `ω`, and on `𝔤` by a
representation `π𝔤`, and let `ρ : 𝔤 → T` be an equivariant linear map with
`ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆`. Let `𝔪` be an invariant complement of `ker ρ` in the coadjoint stabilizer
`𝔤_ν` and `𝔮` an invariant complement of `𝔤_ν` in `𝔤`. Write `W = ρ(𝔤)` and
`V = W^ω ⧸ (W ∩ W^ω)`, on which `K` acts by `πV`, `[u] ↦ [πT k u]`. Then some `K`-equivariant
linear symplectomorphism from

`(𝔪 × 𝔪*) × (𝔮 × V)`, `Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + ν ⁅ζ, ζ'⁆ + ω_V(v, v')`,

where `K` acts on `𝔪`, `𝔮` by `π𝔤`, on `𝔪*` by the dual action and on `V` by `πV`, to `(T, ω)`
sends `(ξ, 0, 0, 0)` to `ρ ξ` and `(0, 0, ζ, 0)` to `ρ ζ`, and sends `(0, 0, 0, [u])`, for
`u ∈ W^ω`, to `u` plus an element of `W`. A continuous finite-dimensional representation of a
compact group is semisimple (`Representation.isSemisimpleRepresentation_of_continuous`). -/
theorem exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction
    [πT.IsSemisimpleRepresentation] (hπT : Representation.IsInvariantForm πT ω.toBilinForm)
    {π𝔤 : Representation ℝ K 𝔤} (hρπ : ∀ k ξ, ρ (π𝔤 k ξ) = πT k (ρ ξ))
    (hρ : ∀ ξ ζ, ω (ρ ξ) (ρ ζ) = ν ⁅ξ, ζ⁆) {𝔪 𝔮 : Subrepresentation π𝔤}
    (h𝔪 : Disjoint (LinearMap.ker ρ) 𝔪.toSubmodule)
    (h𝔪' : LinearMap.ker ρ ⊔ 𝔪.toSubmodule = (lieAnnihilator ℝ 𝔤 ν).toSubmodule)
    (h𝔮 : IsCompl (lieAnnihilator ℝ 𝔤 ν).toSubmodule 𝔮.toSubmodule)
    {πV : Representation ℝ K (ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))}
    (hπV : ∀ k (u u' : ω.orthogonal (LinearMap.range ρ)), (u' : T) = πT k u →
      πV k (Submodule.Quotient.mk u) = Submodule.Quotient.mk u') :
    ∃ e : ((𝔪.toSubmodule × Dual ℝ 𝔪.toSubmodule) ×
        (𝔮.toSubmodule × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))) ≃ₗ[ℝ] T,
      IsSymplectomorphism (cotangentSymplecticForm.prod ((ν.kirillovSymplecticForm h𝔮).prod
        (ω.reduction (ω.orthogonal (LinearMap.range ρ))))) ω e ∧
      (∀ ξ, e ((ξ, 0), (0, 0)) = ρ ξ) ∧ (∀ ζ, e ((0, 0), (ζ, 0)) = ρ ζ) ∧
      (∀ u : ω.orthogonal (LinearMap.range ρ),
        e ((0, 0), (0, Submodule.Quotient.mk u)) - u ∈ LinearMap.range ρ) ∧
      ∀ k x, e (((𝔪.toRepresentation.prod 𝔪.toRepresentation.dual).prod
        (𝔮.toRepresentation.prod πV)) k x) = πT k (e x) := by
  obtain ⟨s, hs, hsπ⟩ := exists_equivariant_lift_reducedSpace (fun k u v ↦ hπT.apply k u v)
    (fun k _ hu ↦ apply_mem_orthogonal_range (fun k u v ↦ hπT.apply k u v) hρπ k hu) hπV
  have := isSemisimpleRepresentation_model hρπ hρ h𝔪 h𝔮 s hs hsπ
  -- `F` sends the orbit directions of `𝔪 × 𝔮` and the lifted slice to `T`, and `G` includes the
  -- same space into the model with zero cotangent component. Both are injective and equivariant,
  -- `ω` pulls back along them to the same form, and their ranges are coisotropic, so the
  -- equivariant Witt extension applies.
  let F := (ρ ∘ₗ 𝔪.toSubmodule.subtype).coprod
    ((ρ ∘ₗ 𝔮.toSubmodule.subtype).coprod ((ω.orthogonal (LinearMap.range ρ)).subtype ∘ₗ s))
  let G := (LinearMap.inl ℝ 𝔪.toSubmodule (Dual ℝ 𝔪.toSubmodule)).prodMap
    (LinearMap.id : (𝔮.toSubmodule × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) →ₗ[ℝ] _)
  have hF (a : 𝔪.toSubmodule) (b : 𝔮.toSubmodule)
      (v : ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ))) :
      F (a, b, v) = ρ a + ρ b + s v := by
    simp [F, add_assoc]
  have := finiteDimensional_model hρ h𝔪 h𝔪' h𝔮 s hs
  obtain ⟨e, he, heι, heπ⟩ := exists_equivariant_isSymplectomorphism_extend_of_isCoisotropic
    (isInvariantForm_model hπT hρπ hρ h𝔮 hπV) hπT (ι₁ := G) (ι₂ := F)
    (σ := 𝔪.toRepresentation.prod (𝔮.toRepresentation.prod πV))
    (fun _ _ h ↦ Prod.ext_iff.2 (by simpa [G] using h)) (injective_coprod_coprod hρ h𝔪 h𝔪' h𝔮 s hs)
    (fun ⟨a, b, v⟩ ⟨a', b', v'⟩ ↦ by
      rw [hF, hF, apply_add_add_apply_add_add hρ h𝔪' s hs]
      simp [G, prod_apply])
    -- `V × {0} × V'` is the product of the Lagrangian zero section of `V × V*` with `V'`.
    (by
      have h : LinearMap.range G = cotangentZeroSection.prod ⊤ := by
        ext; simp [G, LinearMap.range_prodMap, LinearMap.range_inl]
      rw [h]
      exact IsCoisotropic.prod isLagrangian_cotangentZeroSection.isCoisotropic isCoisotropic_top)
    (isCoisotropic_range_coprod_coprod h𝔪' h𝔮 s hs)
    (fun k ⟨a, b, v⟩ ↦ by simp [G])
    (fun k ⟨a, b, v⟩ ↦ by simp [hF, hρπ, hsπ])
  refine ⟨e, he, fun ξ ↦ ?_, fun ζ ↦ ?_, fun u ↦ ?_, heπ⟩
  · simpa [G, hF] using heι (ξ, 0, 0)
  · simpa [G, hF] using heι (0, ζ, 0)
  · have h : e ((0, 0), (0, Submodule.Quotient.mk u)) = s (Submodule.Quotient.mk u) := by
      simpa [G, hF] using heι (0, 0, Submodule.Quotient.mk u)
    have hu := ReducedSpace.mk_eq_mk_iff.1 (hs (Submodule.Quotient.mk u))
    rwa [ω.orthogonal_orthogonal, ← h] at hu

/-- **The linear normal form of Marle and Guillemin–Sternberg.** Let `ρ : 𝔤 → T` be a linear map
into a finite-dimensional symplectic vector space `(T, ω)` with `ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆`, let `𝔪`
be a complement of `ker ρ` in the coadjoint stabilizer `𝔤_ν`, and `𝔮` a complement of `𝔤_ν` in
`𝔤`. Write `W = ρ(𝔤)` and `V = W^ω ⧸ (W ∩ W^ω)` for the reduced space of `W^ω`. Then some linear
symplectomorphism from

`(𝔪 × 𝔪*) × (𝔮 × V)`, `Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + ν ⁅ζ, ζ'⁆ + ω_V(v, v')`

to `(T, ω)` sends `(ξ, 0, 0, 0)` to `ρ ξ` and `(0, 0, ζ, 0)` to `ρ ζ`, and sends `(0, 0, 0, [u])`,
for `u ∈ W^ω`, to `u` plus an element of `W`. This is the case of the trivial group in the
equivariant linear normal form
(`exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`). -/
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
  -- Every representation of the trivial group is semisimple, by Maschke's theorem.
  have : NeZero (Nat.card Unit : ℝ) := ⟨by simp⟩
  obtain ⟨e, he, h₁, h₂, h₃, -⟩ :=
    exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction ω ρ ν
      (K := Unit) (πT := 1) (π𝔤 := 1) (πV := 1) (𝔪 := ⟨𝔪, by simp⟩) (𝔮 := ⟨𝔮, by simp⟩)
      (Representation.isInvariantForm_iff.2 fun _ _ _ ↦ rfl) (fun _ _ ↦ rfl) hρ h𝔪 h𝔪' h𝔮
      fun _ u u' h ↦ congrArg Submodule.Quotient.mk (Subtype.ext h).symm
  exact ⟨e, he, h₁, h₂, h₃⟩

end Equivariant

end SymplecticForm

/-! ### The linear normal form at a point of a manifold -/

open scoped ContDiff

namespace SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ : M → Dual ℝ 𝔤} {x : M}

/-- Where the cocycle of `μ` vanishes, `σ_x(ξ_M, ζ_M) = μ(x) ⁅ξ, ζ⁆`. -/
private theorem symplecticFormAt_eval_eval (hσ : σ.IsNondegenerate)
    (hc : σ.momentCocycle a μ x = 0) (ξ ζ : 𝔤) :
    hσ.symplecticFormAt x (a.eval x ξ) (a.eval x ζ) = μ x ⁅ξ, ζ⁆ := by
  rw [symplecticFormAt_apply, InfinitesimalAction.eval_apply, InfinitesimalAction.eval_apply]
  exact momentCocycle_eq_zero_iff.1 hc ξ ζ

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
      (a.eval x) (μ x) (symplecticFormAt_eval_eval hσ hc) h𝔪 h𝔪' h𝔮
  exact ⟨e, he, fun ξ ↦ (h₁ ξ).trans (a.eval_apply x _), fun ζ ↦ (h₂ ζ).trans (a.eval_apply x _),
    h₃⟩

end SmoothTwoForm.IsNondegenerate


/-! ### The equivariant linear normal form at a point with compact stabilizer -/

section Stabilizer

open _root_.MulAction

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M] {σ : SmoothTwoForm I' M} {μ : M → Dual ℝ (GroupLieAlgebra I G)}
  {x : M}

namespace SmoothTwoForm.IsNondegenerate

/-- The orbit map at `x` intertwines the adjoint action of the stabilizer of `x` with its tangent
representation. -/
private theorem eval_adjointRepresentation (k : stabilizer G x) (ξ : GroupLieAlgebra I G) :
    (InfinitesimalAction.fundamental I G I' M).eval x
        ((Lie.adjointRepresentation ℝ I G).comp (stabilizer G x).subtype k ξ) =
      ((tangentRepresentation fun (g : G) _ ↦ ContMDiffSMul.mdifferentiable_const_smul (I := I)
        (n := ∞) (by simp) g x).toRepresentation : Representation ℝ _ _) k
        ((InfinitesimalAction.fundamental I G I' M).eval x ξ) := by
  simp only [InfinitesimalAction.eval_apply, InfinitesimalAction.fundamental_apply,
    MonoidHom.comp_apply, Subgroup.coe_subtype, Lie.adjointRepresentation_apply]
  exact (tangentRepresentation_fundamentalVectorField _ k ξ).symm

omit [FiniteDimensional ℝ E] [LieGroup I ∞ G] [FiniteDimensional ℝ E'] in
/-- The stabilizer of `x` acts on `T_x M` by linear symplectic maps of `σ_x`. -/
private theorem isInvariantForm_tangentRepresentation (hσ : σ.IsNondegenerate)
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ) :
    Representation.IsInvariantForm (tangentRepresentation fun (g : G) _ ↦
      ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x).toRepresentation
      (hσ.symplecticFormAt x).toBilinForm := by
  have : ContMDiffConstSMul I' ∞ G M := ⟨ContMDiffSMul.contMDiff_const_smul (I := I)⟩
  exact Representation.isInvariantForm_iff.2 fun k u v ↦ by
    simpa only [ContRepresentation.toRepresentation_apply] using
      hσ.symplecticFormAt_tangentRepresentation hσG _ k u v

/-- The stabilizer acts on the symplectic slice by `[u] ↦ [u']` whenever `u' = dh_x u`. -/
private theorem toLinearMapMonoidHom_comp_symplecticSliceRepresentation_mk
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
      (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
    (k : stabilizer G x) (u u' : (hσ.symplecticFormAt x).orthogonal
      ((InfinitesimalAction.fundamental I G I' M).orbitTangent x))
    (h : (u' : TangentSpace I' x) = ((tangentRepresentation fun (g : G) _ ↦
      ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x).toRepresentation :
        Representation ℝ _ (TangentSpace I' x)) k (u : TangentSpace I' x)) :
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      (hσ.symplecticSliceRepresentation hσG) k (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk u' := by
  simp only [MonoidHom.comp_apply, LinearEquiv.automorphismGroup.toLinearMapMonoidHom_apply,
    LinearEquiv.coe_coe, symplecticSliceRepresentation_mk]
  exact congrArg Submodule.Quotient.mk (Subtype.ext h.symm)

variable (hσ : σ.IsNondegenerate)
  (hσG : ∀ g ∈ stabilizer G x, SmoothForm.mpullback (fun y : M ↦ g • y)
    (ContMDiffSMul.contMDiff_const_smul (I := I) g) σ = σ)
  (hc : σ.momentCocycle (InfinitesimalAction.fundamental I G I' M) μ x = 0)
  (hx : IsCompact (stabilizer G x : Set G))
include hσ hσG hc hx

/-- **Invariant complements at a point with compact stabilizer.** Let the stabilizer `H = G_x` be
compact and preserve a nondegenerate two-form `σ`, and let the cocycle of `μ` vanish at `x`. Then
the isotropy algebra `𝔥 = 𝔤_x` and the coadjoint stabilizer `𝔨 = 𝔤_{μ(x)}` are invariant under the
adjoint action of `H`, and they have `H`-invariant complements `𝔤 = 𝔥 ⊕ 𝔪 ⊕ 𝔮` with
`𝔥 ⊕ 𝔪 = 𝔨`. -/
theorem exists_subrepresentation_complements :
    ∃ 𝔪 𝔮 : Subrepresentation ((Lie.adjointRepresentation ℝ I G).comp (stabilizer G x).subtype),
      Disjoint ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule 𝔪.toSubmodule ∧
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule ⊔ 𝔪.toSubmodule =
        (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule ∧
      IsCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule 𝔮.toSubmodule := by
  have := Lie.isSemisimpleRepresentation_adjointRepresentation_comp_subtype (I := I) hx
  rw [InfinitesimalAction.isotropy_toSubmodule]
  exact SymplecticForm.exists_subrepresentation_isCompl_lieAnnihilator
    (isInvariantForm_tangentRepresentation (I := I) hσ hσG) eval_adjointRepresentation
    (symplecticFormAt_eval_eval hσ hc)

/-- **The equivariant linear normal form at a point with compact stabilizer.** Let the stabilizer
`H = G_x` of `x` be compact and preserve a nondegenerate two-form `σ`, and let the cocycle of `μ`
vanish at `x`. For `H`-invariant complements `𝔪` of `𝔤_x` in `𝔤_{μ(x)}` and `𝔮` of `𝔤_{μ(x)}` in
`𝔤` (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_subrepresentation_complements`), some
`H`-equivariant linear symplectomorphism from

`(𝔪 × 𝔪*) × (𝔮 × V)`, `Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + μ(x) ⁅ζ, ζ'⁆ +
ω_V(v, v')`,

where `V` is the symplectic slice at `x` and `H` acts on `𝔪`, `𝔮` by the adjoint action, on `𝔪*`
by the dual action and on `V` by `[u] ↦ [dh_x u]`, to `(T_x M, σ_x)` with the tangent
representation `h ↦ dh_x` sends `(ξ, 0, 0, 0)` to `ξ_M(x)`, `(0, 0, ζ, 0)` to `ζ_M(x)`, and
`(0, 0, 0, [u])` to `u` plus an orbit direction. -/
theorem exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_symplecticSlice
    {𝔪 𝔮 : Subrepresentation ((Lie.adjointRepresentation ℝ I G).comp (stabilizer G x).subtype)}
    (h𝔪 : Disjoint ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
      𝔪.toSubmodule)
    (h𝔪' : ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule ⊔ 𝔪.toSubmodule =
      (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule)
    (h𝔮 : IsCompl (lieAnnihilator ℝ (GroupLieAlgebra I G) (μ x)).toSubmodule 𝔮.toSubmodule) :
    ∃ e : ((𝔪.toSubmodule × Dual ℝ 𝔪.toSubmodule) ×
        (𝔮.toSubmodule × hσ.SymplecticSlice (InfinitesimalAction.fundamental I G I' M) x)) ≃ₗ[ℝ]
        TangentSpace I' x,
      SymplecticForm.IsSymplectomorphism (cotangentSymplecticForm.prod
        (((μ x).kirillovSymplecticForm h𝔮).prod ((hσ.symplecticFormAt x).reduction
          ((hσ.symplecticFormAt x).orthogonal
            ((InfinitesimalAction.fundamental I G I' M).orbitTangent x)))))
        (hσ.symplecticFormAt x) e ∧
      (∀ ξ : 𝔪.toSubmodule, e ((ξ, 0), (0, 0)) = InfinitesimalAction.fundamental I G I' M ξ x) ∧
      (∀ ζ : 𝔮.toSubmodule, e ((0, 0), (ζ, 0)) = InfinitesimalAction.fundamental I G I' M ζ x) ∧
      (∀ u : (hσ.symplecticFormAt x).orthogonal
          ((InfinitesimalAction.fundamental I G I' M).orbitTangent x),
        e ((0, 0), (0, Submodule.Quotient.mk u)) - u ∈
          (InfinitesimalAction.fundamental I G I' M).orbitTangent x) ∧
      ∀ k y, e (((𝔪.toRepresentation.prod 𝔪.toRepresentation.dual).prod (𝔮.toRepresentation.prod
        (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
          (hσ.symplecticSliceRepresentation hσG)))) k y) =
        tangentRepresentation (fun (g : G) _ ↦
          ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x) k (e y) := by
  have := isSemisimpleRepresentation_tangentRepresentation_of_isCompact_stabilizer I (I' := I') hx
    fun (g : G) _ ↦ ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x
  rw [InfinitesimalAction.isotropy_toSubmodule] at h𝔪 h𝔪'
  -- `a.orbitTangent x` occurs in the types of `e`, `u` and the slice representation, so a plain
  -- `rw` with `orbitTangent_eq_range` fails on the motive; we prove the statement for every
  -- subspace `W` equal to `range (a.eval x)` and every representation `πV` on its slice.
  suffices key : ∀ W : Submodule ℝ (TangentSpace I' x),
      W = LinearMap.range ((InfinitesimalAction.fundamental I G I' M).eval x) →
      ∀ πV : Representation ℝ (stabilizer G x)
        ((hσ.symplecticFormAt x).ReducedSpace ((hσ.symplecticFormAt x).orthogonal W)),
      (∀ k (u u' : (hσ.symplecticFormAt x).orthogonal W),
        (u' : TangentSpace I' x) = ((tangentRepresentation fun (g : G) _ ↦
          ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x
            ).toRepresentation : Representation ℝ _ (TangentSpace I' x)) k (u : TangentSpace I' x) →
        πV k (Submodule.Quotient.mk u) = Submodule.Quotient.mk u') →
      ∃ e : ((𝔪.toSubmodule × Dual ℝ 𝔪.toSubmodule) ×
          (𝔮.toSubmodule × (hσ.symplecticFormAt x).ReducedSpace
            ((hσ.symplecticFormAt x).orthogonal W))) ≃ₗ[ℝ] TangentSpace I' x,
        SymplecticForm.IsSymplectomorphism (cotangentSymplecticForm.prod
          (((μ x).kirillovSymplecticForm h𝔮).prod ((hσ.symplecticFormAt x).reduction
            ((hσ.symplecticFormAt x).orthogonal W)))) (hσ.symplecticFormAt x) e ∧
        (∀ ξ : 𝔪.toSubmodule, e ((ξ, 0), (0, 0)) = InfinitesimalAction.fundamental I G I' M ξ x) ∧
        (∀ ζ : 𝔮.toSubmodule, e ((0, 0), (ζ, 0)) = InfinitesimalAction.fundamental I G I' M ζ x) ∧
        (∀ u : (hσ.symplecticFormAt x).orthogonal W,
          e ((0, 0), (0, Submodule.Quotient.mk u)) - u ∈ W) ∧
        ∀ k y, e (((𝔪.toRepresentation.prod 𝔪.toRepresentation.dual).prod
          (𝔮.toRepresentation.prod πV)) k y) = tangentRepresentation (fun (g : G) _ ↦
            ContMDiffSMul.mdifferentiable_const_smul (I := I) (n := ∞) (by simp) g x) k (e y) from
    key _ (InfinitesimalAction.orbitTangent_eq_range _ x) _
      (toLinearMapMonoidHom_comp_symplecticSliceRepresentation_mk hσ hσG)
  rintro W rfl πV hπV
  obtain ⟨e, he, h₁, h₂, h₃, h₄⟩ :=
    SymplecticForm.exists_equivariant_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction
      (hσ.symplecticFormAt x) _ (μ x) (isInvariantForm_tangentRepresentation (I := I) hσ hσG)
      eval_adjointRepresentation (symplecticFormAt_eval_eval hσ hc) h𝔪 h𝔪' h𝔮 hπV
  exact ⟨e, he, fun ξ ↦ (h₁ ξ).trans (InfinitesimalAction.eval_apply _ x _),
    fun ζ ↦ (h₂ ζ).trans (InfinitesimalAction.eval_apply _ x _), h₃, h₄⟩

end SmoothTwoForm.IsNondegenerate

end Stabilizer

end TauCeti
