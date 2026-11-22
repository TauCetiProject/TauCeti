/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Invariants
public import TauCeti.Geometry.Symplectic.Lagrangian.CoisotropicModel
public import TauCeti.RepresentationTheory.InvariantForm
public import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# The equivariant linear coisotropic embedding model

Let a group `G` act linearly on a finite-dimensional symplectic vector space `(V, ω)` by a
representation `ρ` preserving `ω`, and suppose `ρ` is semisimple: every invariant subspace has an
invariant complement. This holds for every continuous finite-dimensional representation of a
compact group (`Representation.isSemisimpleRepresentation_of_continuous`). Let `σ` be a
representation of `G` on `W`, and `ι : W → V` an injective `G`-equivariant linear map with
coisotropic image, pulling `ω` back to an alternating form `B` with kernel `K`. The coisotropic
model `W × K*` of `B` built from a projection `P : W → K`
(`LinearMap.BilinForm.IsAlt.coisotropicModel`) carries the representation of `G` on `W` and the
dual of its restriction to `K`. When `P` is `G`-equivariant, the extension of `ι` to a
symplectomorphism from the model onto `V`
(`LinearMap.BilinForm.IsAlt.exists_isSymplectomorphism_coisotropicModel`) can be chosen
`G`-equivariant
(`LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel`).

Consequently two injective `G`-equivariant linear maps `ι₁ : W → V₁` and `ι₂ : W → V₂` into two
such representations, with coisotropic images and pulling back the same form, differ by a
`G`-equivariant linear symplectomorphism `V₁ ≃ V₂`
(`TauCeti.SymplecticForm.exists_equivariant_isSymplectomorphism_extend_of_isCoisotropic`). This is
the presymplectic Witt extension that compares the tangent representation of the isotropy group
`H` at a point of a Hamiltonian `G`-manifold with that of the Marle–Guillemin–Sternberg local model
`G ×_H (𝔪* × V)`. Witt's extension theorem
(`TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`) has no equivariant analogue for
arbitrary subspaces, even for compact groups: for the zero subspace it would say that any two
symplectic representations of the same dimension are isomorphic, which fails already for the
circle acting on `ℂ` with weights `1` and `2`.

## Construction

Let `R = ι(K)` be the symplectic orthogonal of the image of `ι`, and `D = ι(ker P)`, so that the
image of `ι` is `D ⊕ R`. The subspace `E = D^ω` is invariant and contains `R` as a subspace of half
its dimension. Semisimplicity gives an invariant complement of `R` in `V`, whose intersection `Q`
with `E` is an invariant complement of `R` in `E`. Pairing with `ι(K)` identifies `Q` with `K*`;
write `q₁ : K* → Q` for the inverse. Correcting `q₁` by the map `c : K* → K` with
`a' (c a) = -½ ω(q₁ a, q₁ a')` makes its image isotropic, and the extension is

`(w, a) ↦ ι w + q₁ a + ι (c a)`.

Every choice is invariant or determined by an invariant condition, which makes the extension
equivariant.

## Main results

* `LinearMap.BilinForm.IsAlt.exists_equivariant_isSymplectomorphism_coisotropicModel`:
  equivariant uniqueness of linear coisotropic embeddings.
* `TauCeti.SymplecticForm.exists_equivariant_isSymplectomorphism_extend_of_isCoisotropic`: the
  equivariant Witt extension from coisotropic subspaces.

## References

* M. J. Gotay, *On coisotropic imbeddings of presymplectic manifolds*, Proceedings of the
  American Mathematical Society 84 (1982), 111–114.
* V. Guillemin and S. Sternberg, *A normal form for the moment map*, in *Differential Geometric
  Methods in Mathematical Physics* (Jerusalem, 1982), Math. Phys. Stud. 6, Reidel, 1984, 161–175.
* J.-P. Ortega, T. S. Ratiu, *Momentum Maps and Hamiltonian Reduction*, Progress in Mathematics
  222, Birkhäuser, 2004, Section 7.1 (the symplectic slice and the model space).
-/

public section

open Module TauCeti TauCeti.Representation

namespace LinearMap.BilinForm.IsAlt

variable {W V G : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup V] [Module ℝ V] [Group G]
  {B : LinearMap.BilinForm ℝ W} {σ : Representation ℝ G W} {ρ : Representation ℝ G V}
  {ω : SymplecticForm V} {ι : W →ₗ[ℝ] V} {P : W →ₗ[ℝ] LinearMap.ker B}

section Construction

/-! ### Invariant subspaces attached to an equivariant embedding -/

variable (hρ : IsInvariantForm ρ ω.toBilinForm) (hισ : ∀ g w, ι (σ g w) = ρ g (ι w))
include hρ hισ

/-- The symplectic orthogonal of `ι(ker P)`, for an equivariant `P`, is invariant. -/
private theorem apply_mem_orthogonal_map_ker (hPσ : ∀ g w, (P (σ g w) : W) = σ g (P w)) (g : G)
    {v : V} (hv : v ∈ ω.orthogonal ((LinearMap.ker P).map ι)) :
    ρ g v ∈ ω.orthogonal ((LinearMap.ker P).map ι) := by
  refine SymplecticForm.apply_mem_orthogonal (fun g u v ↦ hρ.apply g u v) ?_ g hv
  rintro g _ ⟨w, hw, rfl⟩
  refine ⟨σ g w, ?_, hισ g w⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hw ⊢
  exact Subtype.ext ((hPσ g w).trans (by rw [hw, ZeroMemClass.coe_zero, map_zero]))

/-- For semisimple `ρ`, the symplectic orthogonal of the image of `ι` has an invariant
complement. -/
private theorem exists_isCompl_orthogonal_range [ρ.IsSemisimpleRepresentation] :
    ∃ Y : Subrepresentation ρ, IsCompl (ω.orthogonal (LinearMap.range ι)) Y.toSubmodule := by
  obtain ⟨Y, hY⟩ := exists_isCompl
    (⟨_, fun g _ hv ↦
      SymplecticForm.apply_mem_orthogonal_range (fun g u v ↦ hρ.apply g u v) hισ g hv⟩ :
      Subrepresentation ρ)
  exact ⟨Y, Subrepresentation.isCompl_toSubmodule.2 hY⟩

end Construction

/-- A vector `ω`-orthogonal to `ι(ker P)` pairs with `ι w` as with `ι (P w)`. -/
private theorem apply_eq_apply_projection (hP : ∀ k : LinearMap.ker B, P k = k) {v : V}
    (hv : v ∈ ω.orthogonal ((LinearMap.ker P).map ι)) (w : W) : ω (ι w) v = ω (ι (P w)) v := by
  have hw : w - P w ∈ LinearMap.ker P := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact (hP (P w)).symm
  have h := (SymplecticForm.mem_orthogonal_iff.1 hv) _ ⟨_, hw, rfl⟩
  simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using h

section Model

variable [FiniteDimensional ℝ V] [ρ.IsSemisimpleRepresentation]
  (hρ : IsInvariantForm ρ ω.toBilinForm) (hι : Function.Injective ι)
  (hω : ∀ w w', ω (ι w) (ι w') = B w w') (hC : ω.IsCoisotropic (LinearMap.range ι))
  (hισ : ∀ g w, ι (σ g w) = ρ g (ι w)) (hP : ∀ k : LinearMap.ker B, P k = k)
  (hPσ : ∀ g w, (P (σ g w) : W) = σ g (P w))
include hρ hι hω hC hισ hP hPσ

/-- An invariant complement `Q` of the radical `R = ι(K)` in `E = ι(ker P)^ω`: it lies in `E`, is
invariant, pairs injectively with `ι(K)`, and has the dimension of `K`. -/
private theorem exists_complement :
    ∃ Q : Submodule ℝ V, Q ≤ ω.orthogonal ((LinearMap.ker P).map ι) ∧
      (∀ g, ∀ v ∈ Q, ρ g v ∈ Q) ∧ (∀ v ∈ Q, (∀ k ∈ LinearMap.ker B, ω (ι k) v = 0) → v = 0) ∧
      finrank ℝ Q = finrank ℝ (LinearMap.ker B) := by
  have : FiniteDimensional ℝ W := .of_injective ι hι
  set R := ω.orthogonal (LinearMap.range ι)
  set E := ω.orthogonal ((LinearMap.ker P).map ι)
  have hRE : R ≤ E := ω.orthogonal_le (LinearMap.map_le_range)
  obtain ⟨Q₀, hQ₀⟩ := exists_isCompl_orthogonal_range hρ hισ
  refine ⟨Q₀.toSubmodule ⊓ E, inf_le_right, fun g v hv ↦
    ⟨Q₀.apply_mem_toSubmodule g hv.1, apply_mem_orthogonal_map_ker hρ hισ hPσ g hv.2⟩,
    fun v hv h ↦ ?_, ?_⟩
  · -- A vector of `E` orthogonal to `ι(K)` is orthogonal to the whole image, so lies in `R`.
    refine Submodule.disjoint_def.1 hQ₀.disjoint v ?_ hv.1
    rw [SymplecticForm.mem_orthogonal_iff]
    rintro _ ⟨w, rfl⟩
    rw [apply_eq_apply_projection hP hv.2]
    exact h _ (P w).property
  · -- `R ⊕ Q = E`, and `dim E = 2 dim K`, `dim R = dim K`.
    have h₁ : R ⊔ Q₀.toSubmodule ⊓ E = E := by
      rw [← sup_inf_assoc_of_le _ hRE, hQ₀.sup_eq_top, top_inf_eq]
    have h₂ : R ⊓ (Q₀.toSubmodule ⊓ E) = ⊥ :=
      eq_bot_mono (inf_le_inf_left _ inf_le_left) hQ₀.inf_eq_bot
    have h₃ := Submodule.finrank_sup_add_finrank_inf_eq R (Q₀.toSubmodule ⊓ E)
    rw [h₁, h₂, finrank_bot] at h₃
    have h₄ : finrank ℝ ((LinearMap.ker P).map ι) + finrank ℝ E = finrank ℝ V :=
      ω.finrank_add_finrank_orthogonal _
    have h₅ := (Submodule.equivMapOfInjective ι hι (LinearMap.ker P)).finrank_eq
    have hR : (LinearMap.ker B).map ι = R := SymplecticForm.map_ker_eq_orthogonal_range ω hω hC
    have h₆ : finrank ℝ (LinearMap.ker B) = finrank ℝ R := by
      rw [← hR]
      exact (Submodule.equivMapOfInjective ι hι (LinearMap.ker B)).finrank_eq
    have h₇ := LinearMap.finrank_range_add_finrank_ker P
    rw [LinearMap.range_eq_top (f := P) |>.2 fun k ↦ ⟨k, hP k⟩, finrank_top] at h₇
    have h₈ := ω.finrank_ker_add_finrank_of_isCoisotropic hι hω hC
    omega

/-- An equivariant linear map `q : K* → V` with `ω(ι w, q a) = a(P w)`. -/
private theorem exists_dual_lift (hσ : IsInvariantForm σ B) :
    ∃ q : Dual ℝ (LinearMap.ker B) →ₗ[ℝ] V, (∀ w a, ω (ι w) (q a) = a (P w)) ∧
      ∀ g a, q (hσ.kerRepresentation.dual g a) = ρ g (q a) := by
  obtain ⟨Q, hQE, hQρ, hQ, hQK⟩ := exists_complement hρ hι hω hC hισ hP hPσ
  have : FiniteDimensional ℝ W := .of_injective ι hι
  -- Pairing with `ι(K)` identifies `Q` with `K*`.
  let Φ : Q →ₗ[ℝ] Dual ℝ (LinearMap.ker B) :=
    (ω.toBilinForm.compl₁₂ (ι ∘ₗ (LinearMap.ker B).subtype) Q.subtype).flip
  have hΦ (x : Q) (k : LinearMap.ker B) : Φ x k = ω (ι k) x := (rfl)
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    refine Subtype.ext (hQ x x.property fun k hk ↦ ?_)
    simpa [hΦ] using LinearMap.congr_fun hx ⟨k, hk⟩
  have hdim : finrank ℝ Q = finrank ℝ (Dual ℝ (LinearMap.ker B)) := by
    rw [hQK, Subspace.dual_finrank_eq]
  let e := Φ.linearEquivOfInjective hinj hdim
  have he (a : Dual ℝ (LinearMap.ker B)) (k : LinearMap.ker B) : ω (ι k) (e.symm a) = a k := by
    rw [← hΦ, ← LinearMap.linearEquivOfInjective_apply hinj hdim, LinearEquiv.apply_symm_apply]
  refine ⟨Q.subtype ∘ₗ e.symm.toLinearMap, fun w a ↦ ?_, fun g a ↦ ?_⟩
  · exact (apply_eq_apply_projection hP (hQE (e.symm a).property) w).trans (he a (P w))
  · -- Both sides lie in `Q` and pair with `ι(K)` in the same way.
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    have hx : ρ g (e.symm a) ∈ Q := hQρ g _ (e.symm a).property
    suffices e.symm (hσ.kerRepresentation.dual g a) = ⟨_, hx⟩ from
      congrArg Subtype.val this
    rw [LinearEquiv.symm_apply_eq]
    ext k
    rw [LinearMap.linearEquivOfInjective_apply, hΦ]
    simp only [Representation.dual_apply, Dual.transpose_apply, LinearMap.comp_apply]
    rw [← he a, IsInvariantForm.coe_kerRepresentation_apply, hισ]
    beta_reduce
    rw [hρ.apply_left, inv_inv]

/-- An equivariant linear map `q : K* → V` with `ω(ι w, q a) = a(P w)` and isotropic image. It
corrects the lift of `exists_dual_lift` by `ι ∘ c`, where `a' (c a) = -½ ω(q₁ a, q₁ a')`. -/
private theorem exists_isotropic_dual_lift (hB : B.IsAlt) (hσ : IsInvariantForm σ B) :
    ∃ q : Dual ℝ (LinearMap.ker B) →ₗ[ℝ] V, (∀ w a, ω (ι w) (q a) = a (P w)) ∧
      (∀ a a', ω (q a) (q a') = 0) ∧ ∀ g a, q (hσ.kerRepresentation.dual g a) = ρ g (q a) := by
  obtain ⟨q₁, hq₁, hq₁ρ⟩ := exists_dual_lift hρ hι hω hC hισ hP hPσ hσ
  -- Unfold the coercion of `ω` to a function, so that this rewrites `ω.toBilinForm`.
  beta_reduce at hq₁
  have : FiniteDimensional ℝ W := .of_injective ι hι
  let c : Dual ℝ (LinearMap.ker B) →ₗ[ℝ] LinearMap.ker B :=
    (-(2 : ℝ)⁻¹) • ((evalEquiv ℝ (LinearMap.ker B)).symm.toLinearMap ∘ₗ
      ω.toBilinForm.compl₁₂ q₁ q₁)
  have hc (a a' : Dual ℝ (LinearMap.ker B)) :
      a' (c a) = -(2 : ℝ)⁻¹ * ω.toBilinForm (q₁ a) (q₁ a') := by
    have h := LinearMap.congr_fun
      ((evalEquiv ℝ (LinearMap.ker B)).apply_symm_apply (ω.toBilinForm.compl₁₂ q₁ q₁ a)) a'
    simp only [evalEquiv_apply, Dual.eval_apply] at h
    simp [c, h]
  -- `ι (c a)` pairs to zero with `ι w`, since `c a` lies in the kernel of `B`.
  have hιc (w : W) (a : Dual ℝ (LinearMap.ker B)) : ω.toBilinForm (ι w) (ι (c a)) = 0 :=
    (hω w (c a)).trans (hB.isRefl.apply_eq_zero_of_mem_ker w (c a).property)
  have hcρ (g : G) (a : Dual ℝ (LinearMap.ker B)) :
      c (hσ.kerRepresentation.dual g a) = hσ.kerRepresentation g (c a) := by
    refine (evalEquiv ℝ (LinearMap.ker B)).injective (LinearMap.ext fun a' ↦ ?_)
    simp only [evalEquiv_apply, Dual.eval_apply]
    rw [hc, hq₁ρ, hρ.apply_left, ← hq₁ρ, ← hc]
    simp [Dual.transpose_apply]
  refine ⟨q₁ + ι ∘ₗ (LinearMap.ker B).subtype ∘ₗ c, fun w a ↦ ?_, fun a a' ↦ ?_, fun g a ↦ ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add,
      hq₁, hιc, add_zero]
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add]
    have h₁ : ω.toBilinForm (ι (c a)) (q₁ a') = a' (c a) := by rw [hq₁, hP]
    have h₂ : ω.toBilinForm (q₁ a) (ι (c a')) = -a (c a') := by
      rw [← ω.isAlt.neg_eq, hq₁, hP]
    have h₃ : ω.toBilinForm (q₁ a') (q₁ a) = -ω.toBilinForm (q₁ a) (q₁ a') :=
      (ω.isAlt.neg_eq _ _).symm
    rw [h₁, h₂, hιc, hc, hc, h₃]
    ring
  · simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add, hq₁ρ,
      hcρ, IsInvariantForm.coe_kerRepresentation_apply, hισ]

end Model

/-- **Equivariant uniqueness of the linear coisotropic embedding.** Let a group `G` act on a
finite-dimensional symplectic vector space `(V, ω)` by a semisimple representation `ρ` preserving
`ω`, and on `W` by a representation `σ`. Let `ι : W → V` be an injective `G`-equivariant linear
map with coisotropic image, pulling `ω` back to `B`, and let the projection `P` of `W` onto the
kernel `K` of `B` be `G`-equivariant. Then `ι` extends to a `G`-equivariant linear
symplectomorphism from the coisotropic model `W × K*` onto `V`, where `G` acts on `W × K*` by `σ`
on `W` and by the dual of its restriction to `K` on `K*`. An equivariant `P` exists when `σ` is
semisimple (`Subrepresentation.exists_equivariant_projection`), for instance when `σ` embeds in `ρ`
(`Representation.IntertwiningMap.isSemisimpleRepresentation_of_injective`). -/
theorem exists_equivariant_isSymplectomorphism_coisotropicModel [FiniteDimensional ℝ V]
    [ρ.IsSemisimpleRepresentation] (hB : B.IsAlt) (hP : ∀ k : LinearMap.ker B, P k = k)
    (hρ : IsInvariantForm ρ ω.toBilinForm) (hσ : IsInvariantForm σ B) (hι : Function.Injective ι)
    (hω : ∀ w w', ω (ι w) (ι w') = B w w') (hC : ω.IsCoisotropic (LinearMap.range ι))
    (hισ : ∀ g w, ι (σ g w) = ρ g (ι w)) (hPσ : ∀ g w, (P (σ g w) : W) = σ g (P w)) :
    ∃ e : (W × Dual ℝ (LinearMap.ker B)) ≃ₗ[ℝ] V,
      SymplecticForm.IsSymplectomorphism (hB.coisotropicModel P hP) ω e ∧
        (∀ w, e (w, 0) = ι w) ∧ ∀ g x, e (σ.prod hσ.kerRepresentation.dual g x) = ρ g (e x) := by
  obtain ⟨q, hq, hqq, hqρ⟩ := exists_isotropic_dual_lift hρ hι hω hC hισ hP hPσ hB hσ
  have : FiniteDimensional ℝ W := .of_injective ι hι
  -- Unfold the coercion of `ω` to a function, so that these rewrite `ω.toBilinForm`.
  beta_reduce at hω hq hqq
  have hF (x y : W × Dual ℝ (LinearMap.ker B)) :
      ω (ι.coprod q x) (ι.coprod q y) = hB.coisotropicModel P hP x y := by
    obtain ⟨w, a⟩ := x
    obtain ⟨w', a'⟩ := y
    have h : ω.toBilinForm (q a) (ι w') = -a (P w') := by rw [← ω.isAlt.neg_eq, hq]
    simp only [LinearMap.coprod_apply, map_add, LinearMap.add_apply, coisotropicModel_apply]
    rw [hω, hq, h, hqq]
    ring
  have hinj : Function.Injective (ι.coprod q) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    refine (hB.coisotropicModel P hP).separatingLeft x fun y ↦ ?_
    simpa [LinearMap.mem_ker.1 hx] using (hF x y).symm
  have hdim : finrank ℝ (W × Dual ℝ (LinearMap.ker B)) = finrank ℝ V := by
    rw [finrank_prod, Subspace.dual_finrank_eq, add_comm,
      ω.finrank_ker_add_finrank_of_isCoisotropic hι hω hC]
  refine ⟨(ι.coprod q).linearEquivOfInjective hinj hdim, ?_, fun w ↦ ?_, fun g x ↦ ?_⟩
  · exact SymplecticForm.isSymplectomorphism_iff.2 hF
  · simp
  · obtain ⟨w, a⟩ := x
    simp [hισ, hqρ, -_root_.Representation.dual_apply]

end LinearMap.BilinForm.IsAlt

namespace TauCeti.SymplecticForm

variable {W V₁ V₂ G : Type*} [AddCommGroup W] [Module ℝ W] [AddCommGroup V₁] [Module ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [Group G]

/-- **The equivariant Witt extension from coisotropic subspaces.** Let a group `G` act on
finite-dimensional symplectic vector spaces `(V₁, ω₁)` and `(V₂, ω₂)` by semisimple
representations preserving the forms, and on `W` by a representation `σ`. Two injective
`G`-equivariant linear maps `ι₁ : W → V₁` and `ι₂ : W → V₂` with coisotropic images, pulling back
the same form, `ω₂(ι₂ w, ι₂ w') = ω₁(ι₁ w, ι₁ w')`, differ by a `G`-equivariant linear
symplectomorphism `e : V₁ ≃ V₂` with `e ∘ ι₁ = ι₂`. -/
theorem exists_equivariant_isSymplectomorphism_extend_of_isCoisotropic [FiniteDimensional ℝ V₁]
    [FiniteDimensional ℝ V₂] {ω₁ : SymplecticForm V₁} {ω₂ : SymplecticForm V₂}
    {ρ₁ : Representation ℝ G V₁} {ρ₂ : Representation ℝ G V₂} [ρ₁.IsSemisimpleRepresentation]
    [ρ₂.IsSemisimpleRepresentation] (hρ₁ : IsInvariantForm ρ₁ ω₁.toBilinForm)
    (hρ₂ : IsInvariantForm ρ₂ ω₂.toBilinForm) {σ : Representation ℝ G W} {ι₁ : W →ₗ[ℝ] V₁}
    {ι₂ : W →ₗ[ℝ] V₂} (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂)
    (hω : ∀ w w', ω₂ (ι₂ w) (ι₂ w') = ω₁ (ι₁ w) (ι₁ w'))
    (hC₁ : ω₁.IsCoisotropic (LinearMap.range ι₁)) (hC₂ : ω₂.IsCoisotropic (LinearMap.range ι₂))
    (hισ₁ : ∀ g w, ι₁ (σ g w) = ρ₁ g (ι₁ w)) (hισ₂ : ∀ g w, ι₂ (σ g w) = ρ₂ g (ι₂ w)) :
    ∃ e : V₁ ≃ₗ[ℝ] V₂, IsSymplectomorphism ω₁ ω₂ e ∧ (∀ w, e (ι₁ w) = ι₂ w) ∧
      ∀ g v, e (ρ₁ g v) = ρ₂ g (e v) := by
  let B : LinearMap.BilinForm ℝ W := ω₁.toBilinForm.compl₁₂ ι₁ ι₁
  have hB : B.IsAlt := fun w ↦ ω₁.self_eq_zero (ι₁ w)
  have hω₁ (w w' : W) : ω₁ (ι₁ w) (ι₁ w') = B w w' := (rfl)
  have hσ : IsInvariantForm σ B := isInvariantForm_iff.2 fun g w w' ↦ by
    simp only [B, LinearMap.compl₁₂_apply, hισ₁, hρ₁.apply]
  -- `σ` embeds in the semisimple `ρ₁`, so the kernel of `B` has an equivariant projection.
  have : σ.IsSemisimpleRepresentation :=
    (ι₁.intertwiningMap_of_isIntertwiningMap σ ρ₁ hισ₁).isSemisimpleRepresentation_of_injective hι₁
  obtain ⟨P, hP, hPσ⟩ := Subrepresentation.exists_equivariant_projection
    (⟨LinearMap.ker B, fun g _ hk ↦ hσ.apply_mem_ker g hk⟩ : Subrepresentation σ)
  obtain ⟨e₁, he₁, he₁ι, he₁ρ⟩ := hB.exists_equivariant_isSymplectomorphism_coisotropicModel hP
    hρ₁ hσ hι₁ hω₁ hC₁ hισ₁ hPσ
  obtain ⟨e₂, he₂, he₂ι, he₂ρ⟩ := hB.exists_equivariant_isSymplectomorphism_coisotropicModel hP
    hρ₂ hσ hι₂ hω hC₂ hισ₂ hPσ
  refine ⟨e₁.symm.trans e₂, he₁.symm.trans he₂, fun w ↦ ?_, fun g v ↦ ?_⟩
  · rw [LinearEquiv.trans_apply, ← he₁ι, e₁.symm_apply_apply, he₂ι]
  · obtain ⟨x, rfl⟩ := e₁.surjective v
    rw [← he₁ρ, LinearEquiv.trans_apply, e₁.symm_apply_apply, he₂ρ, LinearEquiv.trans_apply,
      e₁.symm_apply_apply]

end TauCeti.SymplecticForm
