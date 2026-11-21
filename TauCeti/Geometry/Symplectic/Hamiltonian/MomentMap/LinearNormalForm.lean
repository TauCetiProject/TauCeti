/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Coadjoint
public import TauCeti.Geometry.Symplectic.Cotangent.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.Slice
public import TauCeti.Geometry.Symplectic.WittExtension

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
form a subspace on which `ω` is the restriction of the model form. Since `dim T = 2 dim 𝔪 + dim 𝔮 +
dim V` by the dimension count of the slice, Witt's extension theorem
(`TauCeti.SymplecticForm.exists_isSymplectomorphism_extend_of_injective`) extends this partial
isometry to a symplectomorphism. No finiteness of `𝔤` is needed, and the complements need not be
invariant under any group; the equivariant normal form for a compact stabilizer is a separate
refinement.

## Main results

* `TauCeti.SymplecticForm.exists_isSymplectomorphism_cotangent_prod_kirillov_prod_reduction`: the
  linear normal form for a linear map `ρ` satisfying the moment identity.
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

/-- The orbit directions `ω`-orthogonal to the orbit, `W ∩ W^ω` for `W = ρ(𝔤)`, are those of the
coadjoint stabilizer, and so of any complement `𝔪` of `ker ρ` in it. -/
private theorem range_inf_orthogonal_range {𝔪 : Submodule ℝ 𝔤}
    (h𝔪 : LinearMap.ker ρ ⊔ 𝔪 = (lieAnnihilator ℝ 𝔤 ν).toSubmodule) :
    LinearMap.range ρ ⊓ ω.orthogonal (LinearMap.range ρ) = 𝔪.map ρ := by
  ext u
  simp only [Submodule.mem_inf, LinearMap.mem_range, mem_orthogonal_iff, Submodule.mem_map,
    forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · rintro ⟨⟨ξ, rfl⟩, hξ⟩
    have hK : ξ ∈ (lieAnnihilator ℝ 𝔤 ν).toSubmodule :=
      (mem_lieAnnihilator_iff hρ ξ).2 fun ζ ↦ ω.isRefl.eq_zero (hξ ζ)
    rw [← h𝔪] at hK
    obtain ⟨κ, hκ, m, hm, rfl⟩ := Submodule.mem_sup.1 hK
    exact ⟨m, hm, by rw [map_add, LinearMap.mem_ker.1 hκ, zero_add]⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, rfl⟩, fun ζ ↦ ω.isRefl.eq_zero (apply_eq_zero_of_mem hρ h𝔪 hm ζ)⟩

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

variable [FiniteDimensional ℝ T]

/-- The complements `𝔪` and `𝔮` embed into `T`, so they are finite-dimensional. -/
private theorem finiteDimensional_and_finiteDimensional :
    FiniteDimensional ℝ 𝔪 ∧ FiniteDimensional ℝ 𝔮 := by
  have : FiniteDimensional ℝ (𝔪 × 𝔮) :=
    Module.Finite.of_injective _ (injective_coprod hρ h𝔪 h𝔪' h𝔮)
  exact ⟨Module.Finite.of_injective _ (LinearMap.inl_injective (M₂ := 𝔮)),
    Module.Finite.of_injective _ (LinearMap.inr_injective (M := 𝔪))⟩

/-- The dimension count of the model: `dim T = 2 dim 𝔪 + dim 𝔮 + dim V`. -/
private theorem finrank_model_eq :
    finrank ℝ ((𝔪 × Dual ℝ 𝔪) × (𝔮 × ω.ReducedSpace (ω.orthogonal (LinearMap.range ρ)))) =
      finrank ℝ T := by
  have hP := injective_coprod hρ h𝔪 h𝔪' h𝔮
  obtain ⟨_, _⟩ := finiteDimensional_and_finiteDimensional hρ h𝔪 h𝔪' h𝔮
  have hW : finrank ℝ (LinearMap.range ρ) = finrank ℝ 𝔪 + finrank ℝ 𝔮 := by
    rw [← range_coprod h𝔪' h𝔮, LinearMap.finrank_range_of_inj hP, Module.finrank_prod]
  have hWU :
      finrank ℝ ↥(LinearMap.range ρ ⊓ ω.orthogonal (LinearMap.range ρ)) = finrank ℝ 𝔪 := by
    have h𝔪ρ : 𝔪.map ρ = LinearMap.range (ρ ∘ₗ 𝔪.subtype) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    rw [range_inf_orthogonal_range hρ h𝔪', h𝔪ρ]
    refine LinearMap.finrank_range_of_inj (f := ρ ∘ₗ 𝔪.subtype) fun ξ η h ↦ ?_
    simpa using hP (a₁ := (ξ, 0)) (a₂ := (η, 0)) (by simpa using h)
  have := ω.finrank_reducedSpace_orthogonal_add (LinearMap.range ρ)
  simp only [Module.finrank_prod, Subspace.dual_finrank_eq]
  omega

end Orbit

/-! ### The linear normal form -/

variable [FiniteDimensional ℝ T] (ω ρ ν)

/-- **The linear normal form of Marle and Guillemin–Sternberg.** Let `ρ : 𝔤 → T` be a linear map
into a finite-dimensional symplectic vector space `(T, ω)` with `ω(ρ ξ, ρ ζ) = ν ⁅ξ, ζ⁆`, let `𝔪`
be a complement of `ker ρ` in the coadjoint stabilizer `𝔤_ν`, and `𝔮` a complement of `𝔤_ν` in
`𝔤`. Write `W = ρ(𝔤)` and `V = W^ω ⧸ (W ∩ W^ω)` for the reduced space of `W^ω`. Then some linear
symplectomorphism from

`(𝔪 × 𝔪*) × (𝔮 × V)`, `Ω((ξ, a, ζ, v), (ξ', a', ζ', v')) = a'(ξ) - a(ξ') + ν ⁅ζ, ζ'⁆ + ω_V(v, v')`

to `(T, ω)` sends `(ξ, 0, 0, 0)` to `ρ ξ` and `(0, 0, ζ, 0)` to `ρ ζ`, and sends `(0, 0, 0, [u])`,
for `u ∈ W^ω`, to `u` plus an element of `W`. -/
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
  set U := ω.orthogonal (LinearMap.range ρ)
  -- A linear lift `s` of the reduced space `U ⧸ (W ∩ U)` to `U`.
  obtain ⟨s, hs⟩ := (LinearMap.ker (ω.toBilinForm.restrict U)).mkQ.exists_rightInverse_of_surjective
    (Submodule.range_mkQ _)
  have hs' (v : ω.ReducedSpace U) : Submodule.Quotient.mk (s v) = v := LinearMap.congr_fun hs v
  -- The orbit directions and the lifted slice, as a map `F` from `(𝔪 × 𝔮) × V` to `T`, and the
  -- inclusion `G` of the same space into the model.
  let F : (𝔪 × 𝔮) × ω.ReducedSpace U →ₗ[ℝ] T :=
    ((ρ ∘ₗ 𝔪.subtype).coprod (ρ ∘ₗ 𝔮.subtype)).coprod (U.subtype ∘ₗ s)
  let G : (𝔪 × 𝔮) × ω.ReducedSpace U →ₗ[ℝ] (𝔪 × Dual ℝ 𝔪) × (𝔮 × ω.ReducedSpace U) :=
    ((LinearMap.inl ℝ _ _ ∘ₗ LinearMap.inl ℝ _ _ ∘ₗ LinearMap.fst ℝ _ _) +
      (LinearMap.inr ℝ _ _ ∘ₗ LinearMap.inl ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _)).coprod
      (LinearMap.inr ℝ _ _ ∘ₗ LinearMap.inr ℝ _ _)
  have hF (a : 𝔪) (b : 𝔮) (v : ω.ReducedSpace U) : F ((a, b), v) = ρ a + ρ b + s v := by
    simp [F]
  have hG (a : 𝔪) (b : 𝔮) (v : ω.ReducedSpace U) : G ((a, b), v) = ((a, 0), (b, v)) := by
    simp [G]
  have hGinj : Function.Injective G := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨⟨a, b⟩, v⟩ h
    obtain ⟨rfl, rfl, rfl⟩ : a = 0 ∧ b = 0 ∧ v = 0 := by simpa [LinearMap.mem_ker, hG] using h
    rfl
  obtain ⟨_, _⟩ := finiteDimensional_and_finiteDimensional hρ h𝔪 h𝔪' h𝔮
  obtain ⟨e, he, hext⟩ := exists_isSymplectomorphism_extend_of_injective
    (cotangentSymplecticForm.prod ((ν.kirillovSymplecticForm h𝔮).prod (ω.reduction U))) ω
    (finrank_model_eq hρ h𝔪 h𝔪' h𝔮) hGinj (injective_coprod_coprod hρ h𝔪 h𝔪' h𝔮 s hs')
    fun ⟨⟨a, b⟩, v⟩ ⟨⟨a', b'⟩, v'⟩ ↦ by
      rw [hF, hF, apply_add_add_apply_add_add hρ h𝔪' s hs', hG, hG]
      simp [U]
  refine ⟨e, he, fun ξ ↦ ?_, fun ζ ↦ ?_, fun u ↦ ?_⟩
  · simpa [hG, hF] using hext ((ξ, 0), 0)
  · simpa [hG, hF] using hext ((0, ζ), 0)
  · have h := hext ((0, 0), Submodule.Quotient.mk u)
    rw [hG, hF] at h
    simp only [ZeroMemClass.coe_zero, map_zero, zero_add] at h
    have hu := ReducedSpace.mk_eq_mk_iff.1 (hs' (Submodule.Quotient.mk u))
    rw [ω.orthogonal_orthogonal] at hu
    rwa [h]

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
