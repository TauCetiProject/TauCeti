/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Prod

/-!
# Product linear maps

Mathlib builds the product `e₁.prodCongr e₂` of two linear equivalences, acting on `M₁ × M₂`
componentwise. This file identifies which automorphisms of `M₁ × M₂` arise this way, records the
determinants of such a product and of a block triangular `skewProd` automorphism, and records
that scalar multiplication on a product of modules, read as a linear map over the base of a
scalar tower, is the product map of the two scalar multiplications.

The characterization needs only containment: an automorphism `g` of `M₁ × M₂` that maps
`M₁ × 0` into `M₁ × 0` and `0 × M₂` into `0 × M₂` already acts componentwise, and each component
is then bijective because `g` is. No finiteness is used, so no separate hypothesis on `g⁻¹` is
needed. This is what identifies the image of the orthogonal group of an orthogonal sum of
quadratic forms with the subgroup preserving both summands.

## Main results

* `LinearEquiv.prodCongr_inj`: products of linear equivalences are equal exactly when their
  factors are.
* `LinearEquiv.exists_prodCongr_eq_iff`: an automorphism of `M₁ × M₂` is `e₁.prodCongr e₂` for
  automorphisms `e₁` of `M₁` and `e₂` of `M₂` exactly when it maps each factor into itself.
* `LinearEquiv.det_prodCongr`: `det (e₁.prodCongr e₂) = det e₁ * det e₂` for finite free
  modules; this is `LinearMap.det_prodMap` for linear equivalences.
* `Module.Basis.det_prod`: changes between product bases have the product determinant.
* `Module.Basis.map_prodAssoc_prod`: reassociating a triple product carries the ordered product
  basis `(b × c) × d` to `b × (c × d)`, up to relabelling the index.
* `Module.Basis.prod_reindex_finProdFinEquiv`: concatenating two bases indexed by `Fin n × Fin k`
  and `Fin m × Fin k`, flattened lexicographically, is the flattening of their concatenation
  indexed by `Fin (n + m) × Fin k`.
* `LinearEquiv.det_skewProd`: the same determinant formula for block triangular
  automorphisms, independently of the off-diagonal block.
* `LinearEquiv.nonempty_linearEquiv_of_isUnit_snd_comp_inr`: a linear equivalence `M × P ≃ N × P`
  whose lower-right block is invertible gives `M ≃ N`.
* `LinearMap.finrank_graph`: the graph of a linear map `M → M₂` has the dimension of `M`.
* `LinearMap.coprod_comp_prodComm`: precomposing `f.coprod g` with the exchange of factors gives
  `g.coprod f`, the linear version of `ContinuousLinearMap.coprod_comp_prodComm`.
* `LinearMap.coprod_neg_comp_prodComm`, `LinearMap.map_prodComm_ker_coprod_neg`,
  `LinearMap.surjective_coprod_neg_comm`: the exchange of factors negates `(ξ, η) ↦ α ξ - β η`,
  identifies the fibre product `{(ξ, η) | α ξ = β η}` of `α` and `β` with that of `β`
  and `α`, and transversality, the surjectivity of `(ξ, η) ↦ α ξ - β η`, is symmetric.
* `LinearMap.fiberProductAssoc`: the reassociation `(X ×_T Y) ×_S Z ≃ X ×_T (Y ×_S Z)` of iterated
  fibre products of linear maps, with its components `LinearMap.fiberProductAssoc_apply_fst`,
  `LinearMap.fiberProductAssoc_apply_snd` and those of its inverse
  `LinearMap.fiberProductAssoc_symm_apply_fst`, `LinearMap.fiberProductAssoc_symm_apply_snd`.
* `LinearMap.injective_prodMap`: a product of injective linear maps is injective, stated for the
  coercion of `f.prodMap g`.
* `LinearMap.surjective_coprod_of_comp_left`, `LinearMap.surjective_coprod_of_comp_right`,
  `LinearMap.surjective_coprod_neg_of_comp_right`: surjectivity of `f.coprod g` survives
  removing a precomposition from either map. In particular transversality passes from `α ∘ h`
  and `β`, or from `α` and `β ∘ h`, to `α` and `β`.
* `LinearMap.surjective_coprod_neg_assoc_outer` and its converse
  `LinearMap.surjective_coprod_neg_assoc_symm_outer`: transversality of one bracketing of an
  iterated fibre product gives transversality of the outer fibre product of the other; the inner
  ones follow from the previous item.
* `LinearMap.fiberProductInclusionLeft`, `LinearMap.fiberProductInclusionRight`: for a subspace
  of one factor, the inclusion of the smaller fibre product in the fibre product of `α` and `β`.
* `LinearMap.axes_of_commute_neg_snd`: a linear endomorphism of `R × R × R` preserving the third
  coordinate and commuting with `(x, y, z) ↦ (x, -y, 0)` preserves the first two coordinate axes
  and fixes the third basis vector.
* `TauCeti.LinearMap.lsmul_restrictScalars_prodMap`: multiplication by a scalar on a product of
  modules, read over the base of a scalar tower, is the product map of the two multiplications.
-/

public section

namespace LinearEquiv

section Semiring

variable {R M₁ M₂ : Type*} [Semiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
  [Module R M₂]

/-- Products of linear equivalences are equal exactly when their factors are. -/
@[simp]
theorem prodCongr_inj {M₃ M₄ : Type*} [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid M₄]
    [Module R M₄] {e₁ e₁' : M₁ ≃ₗ[R] M₃} {e₂ e₂' : M₂ ≃ₗ[R] M₄} :
    e₁.prodCongr e₂ = e₁'.prodCongr e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  refine ⟨fun h ↦ ⟨ext fun m ↦ ?_, ext fun m ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ h₁ ▸ h₂ ▸ rfl⟩
  · simpa using congrArg Prod.fst (DFunLike.congr_fun h (m, 0))
  · simpa using congrArg Prod.snd (DFunLike.congr_fun h (0, m))

/-- A linear automorphism of `M₁ × M₂` is a product `e₁.prodCongr e₂` of automorphisms of the
factors exactly when it maps `M₁ × 0` into `M₁ × 0` and `0 × M₂` into `0 × M₂`. -/
theorem exists_prodCongr_eq_iff {g : (M₁ × M₂) ≃ₗ[R] M₁ × M₂} :
    (∃ (e₁ : M₁ ≃ₗ[R] M₁) (e₂ : M₂ ≃ₗ[R] M₂), e₁.prodCongr e₂ = g) ↔
      (∀ m₁, (g (m₁, 0)).2 = 0) ∧ ∀ m₂, (g (0, m₂)).1 = 0 := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rintro ⟨e₁, e₂, rfl⟩
    exact ⟨fun _ ↦ by simp, fun _ ↦ by simp⟩
  -- Preserving both factors makes `g` act componentwise.
  have hg (x : M₁ × M₂) : g x = ((g (x.1, 0)).1, (g (0, x.2)).2) := by
    conv_lhs => rw [← Prod.fst_add_snd x, map_add]
    ext <;> simp [h₁, h₂]
  have hb₁ : Function.Bijective
      (LinearMap.fst R M₁ M₂ ∘ₗ g.toLinearMap ∘ₗ LinearMap.inl R M₁ M₂) := by
    refine ⟨fun a b hab ↦ ?_, fun y ↦ ⟨(g.symm (y, 0)).1, ?_⟩⟩
    · have : g (a, 0) = g (b, 0) := Prod.ext hab (by rw [h₁, h₁])
      simpa using g.injective this
    · simpa using (congrArg Prod.fst (hg (g.symm (y, 0)))).symm
  have hb₂ : Function.Bijective
      (LinearMap.snd R M₁ M₂ ∘ₗ g.toLinearMap ∘ₗ LinearMap.inr R M₁ M₂) := by
    refine ⟨fun a b hab ↦ ?_, fun y ↦ ⟨(g.symm (0, y)).2, ?_⟩⟩
    · have : g (0, a) = g (0, b) := Prod.ext (by rw [h₂, h₂]) hab
      simpa using g.injective this
    · simpa using (congrArg Prod.snd (hg (g.symm (0, y)))).symm
  refine ⟨ofBijective _ hb₁, ofBijective _ hb₂, ?_⟩
  ext x <;> simp [hg x]

end Semiring

section CommRing

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [Module.Free R M₁] [Module.Finite R M₁] [Module.Free R M₂] [Module.Finite R M₂]

/-- The determinant of a product of linear automorphisms of finite free modules is the product of
their determinants. -/
@[simp]
theorem det_prodCongr (e₁ : M₁ ≃ₗ[R] M₁) (e₂ : M₂ ≃ₗ[R] M₂) :
    (e₁.prodCongr e₂).det = e₁.det * e₂.det := by
  ext
  simp [coe_det, LinearMap.det_prodMap]

/-- The determinant of a block triangular linear automorphism is the product of the
determinants of its diagonal blocks. -/
@[simp]
theorem det_skewProd (e₁ : M₁ ≃ₗ[R] M₁) (e₂ : M₂ ≃ₗ[R] M₂) (f : M₁ →ₗ[R] M₂) :
    (e₁.skewProd e₂ f).det = e₁.det * e₂.det := by
  classical
  let b₁ := Module.Free.chooseBasis R M₁
  let b₂ := Module.Free.chooseBasis R M₂
  have hmat : LinearMap.toMatrix (b₁.prod b₂) (b₁.prod b₂)
      (e₁.skewProd e₂ f).toLinearMap =
      Matrix.fromBlocks (LinearMap.toMatrix b₁ b₁ e₁.toLinearMap) 0
        (LinearMap.toMatrix b₁ b₂ f) (LinearMap.toMatrix b₂ b₂ e₂.toLinearMap) := by
    ext i j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix_apply, LinearEquiv.skewProd_apply]
  apply Units.ext
  simp only [coe_det, Units.val_mul]
  rw [← LinearMap.det_toMatrix (b₁.prod b₂), hmat, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

end CommRing

section Cancellation

variable {A : Type*} [Semiring A] {M N : Type*} [AddCommMonoid M] [Module A M]
  [AddCommMonoid N] [Module A N] {P : Type*} [AddCommGroup P] [Module A P]

/-- **Cancellation from an invertible lower-right block.** A linear equivalence `M × P ≃ N × P`
whose lower-right block `P → P` is invertible induces a linear equivalence `M ≃ N`. -/
theorem nonempty_linearEquiv_of_isUnit_snd_comp_inr (e₁ : (M × P) ≃ₗ[A] (N × P))
    (he₁ : IsUnit ((LinearMap.snd A N P).comp
      ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P)))) :
    Nonempty (M ≃ₗ[A] N) := by
  -- Clear the lower-left block. The resulting triangular equivalence restricts to an
  -- equivalence on pairs with second coordinate zero, so no subtraction in `M` or `N` is needed.
  let c₁ : M →ₗ[A] P := (LinearMap.snd A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inl A M P))
  let d₁ : Module.End A P := (LinearMap.snd A N P).comp
    ((e₁ : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inr A M P))
  let ed : P ≃ₗ[A] P := LinearEquiv.ofBijective d₁ ((Module.End.isUnit_iff d₁).mp he₁)
  let sourceShear : (M × P) ≃ₗ[A] (M × P) :=
    (LinearEquiv.refl A M).skewProd (LinearEquiv.refl A P)
      (-((ed.symm : P →ₗ[A] P).comp c₁))
  let triangular := sourceShear.trans e₁
  let s : M →ₗ[A] N := (LinearMap.fst A N P).comp
    ((triangular : (M × P) →ₗ[A] (N × P)).comp (LinearMap.inl A M P))
  have he₁_snd (m : M) (p : P) : (e₁ (m, p)).2 = c₁ m + d₁ p := by
    rw [← Prod.fst_add_snd (m, p), map_add]
    rfl
  have htriangular (m : M) (p : P) : (triangular (m, p)).2 = d₁ p := by
    simp only [triangular, sourceShear, LinearEquiv.trans_apply,
      LinearEquiv.skewProd_apply, LinearEquiv.refl_apply, LinearMap.neg_apply,
      LinearMap.comp_apply]
    rw [he₁_snd]
    have hd_inv (x : P) : d₁ (ed.symm x) = x := ed.apply_symm_apply x
    simp [hd_inv]
  have hs_injective : Function.Injective s := by
    intro m m' hmm'
    have hpair : triangular (m, 0) = triangular (m', 0) := by
      apply Prod.ext
      · exact hmm'
      · rw [htriangular, htriangular]
    exact congrArg Prod.fst (triangular.injective hpair)
  have hs_surjective : Function.Surjective s := by
    intro n
    obtain ⟨⟨m, p⟩, hmp⟩ := triangular.surjective (n, 0)
    have hp : d₁ p = 0 := by simpa only [htriangular] using congrArg Prod.snd hmp
    have hp : p = 0 := ed.injective (hp.trans ed.map_zero.symm)
    subst p
    exact ⟨m, congrArg Prod.fst hmp⟩
  exact ⟨LinearEquiv.ofBijective s ⟨hs_injective, hs_surjective⟩⟩

end Cancellation

end LinearEquiv

namespace LinearMap

/-- The graph of a linear map `f : M → M₂` has the dimension of `M`. -/
theorem finrank_graph {R M M₂ : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M₂] [Module R M₂] (f : M →ₗ[R] M₂) :
    Module.finrank R (graph f) = Module.finrank R M := by
  rw [graph_eq_range_prod, finrank_range_of_inj]
  intro x y h
  exact congr(($h).1)

section Semiring

variable {R M₁ M₂ M₃ : Type*} [Semiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
  [Module R M₂] [AddCommMonoid M₃] [Module R M₃]

/-- Precomposing a map on a product with the exchange of the factors exchanges its components. -/
theorem coprod_comp_prodComm (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
    f.coprod g ∘ₗ (LinearEquiv.prodComm R M₂ M₁).toLinearMap = g.coprod f := by
  ext <;> simp

variable {M₄ : Type*} [AddCommMonoid M₄] [Module R M₄]

/-- A product of injective linear maps is injective, stated for the coercion of `f.prodMap g`. -/
theorem injective_prodMap {f : M₁ →ₗ[R] M₃} {g : M₂ →ₗ[R] M₄} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (f.prodMap g) :=
  hf.prodMap hg

/-- If `(x, y) ↦ f (h x) + g y` is surjective, then so is `(x, y) ↦ f x + g y`. -/
theorem surjective_coprod_of_comp_left {f : M₁ →ₗ[R] M₃} {g : M₂ →ₗ[R] M₃} {h : M₄ →ₗ[R] M₁}
    (H : Function.Surjective ((f ∘ₗ h).coprod g)) : Function.Surjective (f.coprod g) := fun y ↦ by
  obtain ⟨x, hx⟩ := H y
  exact ⟨h.prodMap LinearMap.id x, by simpa using hx⟩

/-- If `(x, y) ↦ f x + g (h y)` is surjective, then so is `(x, y) ↦ f x + g y`. -/
theorem surjective_coprod_of_comp_right {f : M₁ →ₗ[R] M₃} {g : M₂ →ₗ[R] M₃} {h : M₄ →ₗ[R] M₂}
    (H : Function.Surjective (f.coprod (g ∘ₗ h))) : Function.Surjective (f.coprod g) := fun y ↦ by
  obtain ⟨x, hx⟩ := H y
  exact ⟨LinearMap.id.prodMap h x, by simpa using hx⟩

end Semiring

section Ring

variable {R X Y T : Type*} [Ring R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup T] [Module R T] (α : X →ₗ[R] T) (β : Y →ₗ[R] T)

/-- Precomposing `(η, ξ) ↦ β η - α ξ` with the exchange of factors gives the negative of
`(ξ, η) ↦ α ξ - β η`. -/
theorem coprod_neg_comp_prodComm :
    β.coprod (-α) ∘ₗ (LinearEquiv.prodComm R X Y).toLinearMap = -α.coprod (-β) := by
  rw [coprod_comp_prodComm]
  ext <;> simp

/-- The exchange of factors carries the fibre product `{(ξ, η) | α ξ = β η}` of `α` and `β`
onto that of `β` and `α`. -/
theorem map_prodComm_ker_coprod_neg :
    (ker (α.coprod (-β))).map (LinearEquiv.prodComm R X Y : X × Y →ₗ[R] Y × X) =
      ker (β.coprod (-α)) := by
  rw [Submodule.map_equiv_eq_comap_symm, ← ker_comp, LinearEquiv.symm_prodComm,
    coprod_neg_comp_prodComm, ker_neg]

/-- Transversality of `α` and `β`, the surjectivity of `(ξ, η) ↦ α ξ - β η`, is symmetric. -/
theorem surjective_coprod_neg_comm (h : Function.Surjective (α.coprod (-β))) :
    Function.Surjective (β.coprod (-α)) := by
  intro z
  obtain ⟨w, hw⟩ := h (-z)
  refine ⟨LinearEquiv.prodComm R X Y w, ?_⟩
  have hw' := LinearMap.congr_fun (coprod_neg_comp_prodComm α β) w
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.neg_apply] at hw'
  rw [hw', hw, neg_neg]

section Assoc

variable {R X Y Z T S : Type*} [Ring R] [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y] [AddCommGroup Z] [Module R Z] [AddCommGroup T] [Module R T] [AddCommGroup S]
  [Module R S] (α : X →ₗ[R] T) (β : Y →ₗ[R] T) (γ : Y →ₗ[R] S) (δ : Z →ₗ[R] S)

/-- The reassociation `(X ×_T Y) ×_S Z ≃ X ×_T (Y ×_S Z)` of iterated fibre products, for
`α : X → T`, `β : Y → T`, `γ : Y → S` and `δ : Z → S`: both sides consist of the triples
`(ξ, η, ζ)` with `α ξ = β η` and `γ η = δ ζ`, and the equivalence regroups them. On the left the
second fibre product is taken along `γ` restricted to `X ×_T Y`, and on the right the first is
taken along `β` restricted to `Y ×_S Z`. -/
def fiberProductAssoc :
    ker ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ)) ≃ₗ[R]
      ker (α.coprod (-(β ∘ₗ fst R Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype))) where
  -- Without `map_coe_ker`, `simp` unfolds each membership hypothesis instead of reducing it to
  -- `True` through the membership of an inner component.
  toFun r := ⟨(r.1.1.1.1, ⟨(r.1.1.1.2, r.1.2), by simpa [-map_coe_ker] using mem_ker.1 r.2⟩),
    by simpa [-map_coe_ker] using mem_ker.1 r.1.1.2⟩
  invFun r := ⟨(⟨(r.1.1, r.1.2.1.1), by simpa [-map_coe_ker] using mem_ker.1 r.2⟩, r.1.2.1.2),
    by simpa [-map_coe_ker] using mem_ker.1 r.1.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {α β γ δ}

/-- The `X`-component of the reassociation of `((ξ, η), ζ)` is `ξ`. -/
@[simp]
theorem fiberProductAssoc_apply_fst
    (r : ker ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ))) :
    (fiberProductAssoc α β γ δ r).1.1 = r.1.1.1.1 :=
 (rfl)

/-- The `Y ×_S Z`-component of the reassociation of `((ξ, η), ζ)` is `(η, ζ)`. -/
@[simp]
theorem fiberProductAssoc_apply_snd
    (r : ker ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ))) :
    ((fiberProductAssoc α β γ δ r).1.2 : Y × Z) = (r.1.1.1.2, r.1.2) :=
 (rfl)

/-- The `X ×_T Y`-component of the inverse reassociation of `(ξ, (η, ζ))` is `(ξ, η)`. -/
@[simp]
theorem fiberProductAssoc_symm_apply_fst
    (r : ker (α.coprod (-(β ∘ₗ fst R Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype)))) :
    (((fiberProductAssoc α β γ δ).symm r).1.1 : X × Y) = (r.1.1, r.1.2.1.1) :=
 (rfl)

/-- The `Z`-component of the inverse reassociation of `(ξ, (η, ζ))` is `ζ`. -/
@[simp]
theorem fiberProductAssoc_symm_apply_snd
    (r : ker (α.coprod (-(β ∘ₗ fst R Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype)))) :
    ((fiberProductAssoc α β γ δ).symm r).1.2 = r.1.2.1.2 :=
 (rfl)

/-- The reassociation is the restriction of `(X × Y) × Z ≃ X × (Y × Z)`: viewed in `X × (Y × Z)`,
the image of `((ξ, η), ζ)` is `(ξ, (η, ζ))`. -/
theorem prodMap_subtype_fiberProductAssoc_apply
    (r : ker ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ))) :
    (LinearMap.id.prodMap (ker (γ.coprod (-δ))).subtype)
        (fiberProductAssoc α β γ δ r : X × ker (γ.coprod (-δ))) =
      LinearEquiv.prodAssoc R X Y Z
        ((ker (α.coprod (-β))).subtype.prodMap LinearMap.id (r : ker (α.coprod (-β)) × Z)) := by
  ext <;> simp

/-- Transversality of the left bracketing `(X ×_T Y) ×_S Z` gives transversality of the outer
fibre product `X ×_T (Y ×_S Z)` of the right bracketing: `α` and `β` restricted to `Y ×_S Z` are
transverse. -/
theorem surjective_coprod_neg_assoc_outer (h₁ : Function.Surjective (α.coprod (-β)))
    (h₁₂ : Function.Surjective
      ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ))) :
    Function.Surjective (α.coprod (-(β ∘ₗ fst R Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype))) := by
  -- Correct a solution `(ξ, η)` of `α ξ - β η = τ` by a point `(ξ₀, η₀)` of `X ×_T Y` with
  -- `γ η₀ - δ ζ₀ = γ η`, so that `η - η₀` satisfies `γ (η - η₀) = δ (-ζ₀)`.
  intro τ
  obtain ⟨⟨ξ, η⟩, hτ⟩ := h₁ τ
  obtain ⟨⟨⟨⟨ξ₀, η₀⟩, h₀⟩, ζ₀⟩, hw⟩ := h₁₂ (γ η)
  simp only [coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg] at hτ
  simp only [mem_ker, coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg, sub_eq_zero] at h₀
  simp only [coprod_apply, comp_apply, Submodule.subtype_apply, snd_apply, LinearMap.neg_apply,
    ← sub_eq_add_neg] at hw
  refine ⟨(ξ - ξ₀, ⟨(η - η₀, -ζ₀), ?_⟩), ?_⟩
  · simp only [mem_ker, coprod_apply, LinearMap.neg_apply, map_sub, map_neg, ← hw]
    abel
  · simp only [coprod_apply, comp_apply, Submodule.subtype_apply, fst_apply, LinearMap.neg_apply,
      map_sub,
      h₀, ← hτ]
    abel

/-- Transversality of the right bracketing `X ×_T (Y ×_S Z)` gives transversality of the outer
fibre product `(X ×_T Y) ×_S Z` of the left bracketing: `γ` restricted to `X ×_T Y` and `δ` are
transverse. -/
theorem surjective_coprod_neg_assoc_symm_outer (h₂ : Function.Surjective (γ.coprod (-δ)))
    (h₂₂ : Function.Surjective
      (α.coprod (-(β ∘ₗ fst R Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype)))) :
    Function.Surjective ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ)) := by
  -- Correct a solution `(η, ζ)` of `γ η - δ ζ = σ` by a point `(η₀, ζ₀)` of `Y ×_S Z` with
  -- `α ξ₀ - β η₀ = β η`, so that `η + η₀` satisfies `α ξ₀ = β (η + η₀)`.
  intro σ
  obtain ⟨⟨η, ζ⟩, hσ⟩ := h₂ σ
  obtain ⟨⟨ξ₀, ⟨⟨η₀, ζ₀⟩, h₀⟩⟩, hw⟩ := h₂₂ (β η)
  simp only [coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg] at hσ
  simp only [mem_ker, coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg, sub_eq_zero] at h₀
  simp only [coprod_apply, comp_apply, Submodule.subtype_apply, fst_apply, LinearMap.neg_apply,
    ← sub_eq_add_neg] at hw
  refine ⟨(⟨(ξ₀, η + η₀), ?_⟩, ζ + ζ₀), ?_⟩
  · simp only [mem_ker, coprod_apply, LinearMap.neg_apply, map_add, ← hw]
    abel
  · simp only [coprod_apply, comp_apply, Submodule.subtype_apply, snd_apply, LinearMap.neg_apply,
      map_add,
      h₀, ← hσ]
    abel

end Assoc

end Ring

section FiberProductInclusion

variable {R X Y T : Type*} [Ring R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
  [AddCommGroup T] [Module R T] (α : X →ₗ[R] T) (β : Y →ₗ[R] T)

/-- For a subspace `p` of `X`, the fibre product of `α ∘ p.subtype` and `β` lies in that of `α`
and `β`: the inclusion `p × Y → X × Y` restricts to the fibre products. -/
def fiberProductInclusionLeft (p : Submodule R X) :
    ker ((α ∘ₗ p.subtype).coprod (-β)) →ₗ[R] ker (α.coprod (-β)) :=
  (p.subtype.prodMap LinearMap.id).restrict fun z hz ↦ by simpa using hz

/-- For a subspace `p` of `Y`, the fibre product of `α` and `β ∘ p.subtype` lies in that of `α`
and `β`: the inclusion `X × p → X × Y` restricts to the fibre products. -/
def fiberProductInclusionRight (p : Submodule R Y) :
    ker (α.coprod (-(β ∘ₗ p.subtype))) →ₗ[R] ker (α.coprod (-β)) :=
  (LinearMap.id.prodMap p.subtype).restrict fun z hz ↦ by simpa using hz

variable {α β}

/-- The inclusion `p ×_T Y → X ×_T Y` is the inclusion `p × Y → X × Y` on underlying pairs. -/
@[simp]
theorem coe_fiberProductInclusionLeft_apply (p : Submodule R X)
    (z : ker ((α ∘ₗ p.subtype).coprod (-β))) :
    (fiberProductInclusionLeft α β p z : X × Y) = p.subtype.prodMap LinearMap.id z :=
  (rfl)

/-- The inclusion `X ×_T p → X ×_T Y` is the inclusion `X × p → X × Y` on underlying pairs. -/
@[simp]
theorem coe_fiberProductInclusionRight_apply (p : Submodule R Y)
    (z : ker (α.coprod (-(β ∘ₗ p.subtype)))) :
    (fiberProductInclusionRight α β p z : X × Y) = LinearMap.id.prodMap p.subtype z :=
  (rfl)

/-- The inclusion `p ×_T Y → X ×_T Y` is injective. -/
theorem fiberProductInclusionLeft_injective (p : Submodule R X) :
    Function.Injective (fiberProductInclusionLeft α β p) := fun _ _ h ↦
  Subtype.ext (Prod.ext (Subtype.ext congr(($h : X × Y).1)) congr(($h : X × Y).2))

/-- The inclusion `X ×_T p → X ×_T Y` is injective. -/
theorem fiberProductInclusionRight_injective (p : Submodule R Y) :
    Function.Injective (fiberProductInclusionRight α β p) := fun _ _ h ↦
  Subtype.ext (Prod.ext congr(($h : X × Y).1) (Subtype.ext congr(($h : X × Y).2)))

/-- A point of the fibre product of `α` and `β` lies in `p ×_T Y` exactly when its first
component lies in `p`. -/
theorem mem_range_fiberProductInclusionLeft {p : Submodule R X} {v : ker (α.coprod (-β))} :
    v ∈ range (fiberProductInclusionLeft α β p) ↔ (v : X × Y).1 ∈ p := by
  refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun h ↦ ⟨⟨(⟨_, h⟩, (v : X × Y).2), ?_⟩, Subtype.ext (by simp)⟩⟩
  · rw [← hz, coe_fiberProductInclusionLeft_apply]
    exact (z : p × Y).1.2
  · have hv := mem_ker.1 v.2
    rw [coprod_apply] at hv
    simpa using hv

/-- A point of the fibre product of `α` and `β` lies in `X ×_T p` exactly when its second
component lies in `p`. -/
theorem mem_range_fiberProductInclusionRight {p : Submodule R Y} {v : ker (α.coprod (-β))} :
    v ∈ range (fiberProductInclusionRight α β p) ↔ (v : X × Y).2 ∈ p := by
  refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun h ↦ ⟨⟨((v : X × Y).1, ⟨_, h⟩), ?_⟩, Subtype.ext (by simp)⟩⟩
  · rw [← hz, coe_fiberProductInclusionRight_apply]
    exact (z : X × p).2.2
  · have hv := mem_ker.1 v.2
    rw [coprod_apply] at hv
    simpa using hv

/-- Transversality of `α` and `β ∘ h` implies that of `α` and `β`. -/
theorem surjective_coprod_neg_of_comp_right {P : Type*} [AddCommGroup P] [Module R P]
    {h : P →ₗ[R] Y} (H : Function.Surjective (α.coprod (-(β ∘ₗ h)))) :
    Function.Surjective (α.coprod (-β)) :=
  surjective_coprod_of_comp_right (h := h) (by rwa [← neg_comp] at H)

end FiberProductInclusion

end LinearMap

namespace Module.Basis

variable {R E F ι κ : Type*} [CommRing R] [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The determinant of a change between product bases is the product of the two factor
change-of-basis determinants. -/
theorem det_prod (b b' : Basis ι R E) (c c' : Basis κ R F) :
    (b.prod c).det (b'.prod c') = b.det b' * c.det c' := by
  rw [Basis.det_apply, Basis.det_apply, Basis.det_apply]
  have he : (b.prod c).toMatrix (b'.prod c') =
      Matrix.fromBlocks (b.toMatrix b') 0 0 (c.toMatrix c') := by
    ext i j
    cases i <;> cases j <;>
      simp [Basis.toMatrix_apply]
  rw [he, Matrix.det_fromBlocks_zero₂₁]

/-- Reassociating `(E × F) × G` as `E × (F × G)` carries the ordered product basis `(b × c) × d`,
indexed by `Fin (m + n + p)`, to the ordered product basis `b × (c × d)`, reindexed along
`m + n + p = m + (n + p)`. -/
theorem map_prodAssoc_prod {R E F G : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] [AddCommMonoid G] [Module R G] {m n p : ℕ}
    (b : Basis (Fin m) R E) (c : Basis (Fin n) R F) (d : Basis (Fin p) R G) :
    ((((b.prod c).reindex finSumFinEquiv).prod d).reindex finSumFinEquiv).map
        (LinearEquiv.prodAssoc R E F G) =
      ((b.prod ((c.prod d).reindex finSumFinEquiv)).reindex finSumFinEquiv).reindex
        (finCongr (add_assoc m n p).symm) := by
  refine Basis.eq_of_apply_eq fun i ↦ ?_
  induction i using Fin.addCases with
  | left j =>
    induction j using Fin.addCases with
    | left k =>
      have h : Fin.cast (add_assoc m n p) (Fin.castAdd p (Fin.castAdd n k)) =
          Fin.castAdd (n + p) k := Fin.ext rfl
      simp [Basis.prod_apply, h]
    | right k =>
      have h : Fin.cast (add_assoc m n p) (Fin.castAdd p (Fin.natAdd m k)) =
          Fin.natAdd m (Fin.castAdd p k) := Fin.ext rfl
      simp [Basis.prod_apply, h]
  | right k =>
    have h : Fin.cast (add_assoc m n p) (Fin.natAdd (m + n) k) =
        Fin.natAdd m (Fin.natAdd n k) := Fin.ext (Nat.add_assoc m n k)
    simp [Basis.prod_apply, h]

/-- Flattening bases `b` and `c` indexed by `Fin n × Fin k` and `Fin m × Fin k` along
`finProdFinEquiv` and concatenating them gives the basis `b ⊕ c` indexed by `Fin (n + m) × Fin k`,
flattened along `finProdFinEquiv`: position `k i + a` lies in the first block exactly when
`i < n`. -/
theorem prod_reindex_finProdFinEquiv {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] {n m k p q r : ℕ} (b : Basis (Fin n × Fin k) R E)
    (c : Basis (Fin m × Fin k) R F) (hp : n * k = p) (hq : m * k = q) (hr : (n + m) * k = r)
    (hpq : p + q = r) :
    ((b.reindex (finProdFinEquiv.trans (finCongr hp))).prod
        (c.reindex (finProdFinEquiv.trans (finCongr hq)))).reindex
        (finSumFinEquiv.trans (finCongr hpq)) =
      ((b.prod c).reindex ((Equiv.sumProdDistrib _ _ _).symm.trans
        (finSumFinEquiv.prodCongr (Equiv.refl _)))).reindex
        (finProdFinEquiv.trans (finCongr hr)) := by
  set e : (Fin n × Fin k) ⊕ (Fin m × Fin k) ≃ Fin (n + m) × Fin k :=
    (Equiv.sumProdDistrib _ _ _).symm.trans (finSumFinEquiv.prodCongr (Equiv.refl _))
  set G := (Equiv.sumCongr (finProdFinEquiv.trans (finCongr hp))
    (finProdFinEquiv.trans (finCongr hq))).trans (finSumFinEquiv.trans (finCongr hpq))
  have hG (x) : G x = finProdFinEquiv.trans (finCongr hr) (e x) := by
    rcases x with ⟨i, a⟩ | ⟨j, a⟩
    · ext
      simp [G, e]
    · ext
      simp only [Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.coe_trans, Sum.map_inr,
        Function.comp_apply, finCongr_apply, finSumFinEquiv_apply_right, Fin.val_cast,
        Fin.val_natAdd, finProdFinEquiv_apply_val, Equiv.sumProdDistrib_symm_apply_right,
        Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id_eq, G, e]
      rw [← hp]
      ring
  refine Basis.eq_of_apply_eq fun x ↦ ?_
  obtain ⟨x, rfl⟩ := G.surjective x
  conv_rhs => rw [Basis.reindex_apply, Basis.reindex_apply, hG, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  rcases x with x | x <;> simp [G, Basis.reindex_apply, Basis.prod_apply]

end Module.Basis

namespace LinearMap

variable {R : Type*} [Ring R] [HasUniqueDiv R]

/-- A linear endomorphism of `R × R × R` that preserves the third coordinate and intertwines the
map `(x, y, z) ↦ (x, -y, 0)` with itself preserves the first two coordinate axes and fixes the
third basis vector. -/
theorem axes_of_commute_neg_snd (A : R × R × R →ₗ[R] R × R × R) (hz : ∀ u, (A u).2.2 = u.2.2)
    (hc : ∀ u : R × R × R, A (u.1, -u.2.1, 0) = ((A u).1, -(A u).2.1, 0)) :
    A (1, 0, 0) = ((A (1, 0, 0)).1, 0, 0) ∧ A (0, 1, 0) = (0, (A (0, 1, 0)).2.1, 0) ∧
      A (0, 0, 1) = (0, 0, 1) := by
  have h₁ : A (1, 0, 0) = ((A (1, 0, 0)).1, 0, 0) := by
    have h := congrArg (fun v : R × R × R => v.2.1) (hc (1, 0, 0))
    simp only [neg_zero] at h
    exact Prod.ext rfl (Prod.ext (self_eq_neg.1 h) (hz (1, 0, 0)))
  have h₂ : A (0, 1, 0) = (0, (A (0, 1, 0)).2.1, 0) := by
    have h := congrArg Prod.fst (hc (0, 1, 0))
    have hneg : A (0, -1, 0) = -A (0, 1, 0) := by
      simpa using A.map_neg (0, 1, 0)
    rw [hneg] at h
    simp only [Prod.fst_neg] at h
    exact Prod.ext (neg_eq_self.1 h) (Prod.ext rfl (hz (0, 1, 0)))
  have h₃ : A (0, 0, 1) = (0, 0, 1) := by
    have h := hc (0, 0, 1)
    simp only [neg_zero] at h
    have hzero : A (0, 0, 0) = 0 := A.map_zero
    rw [hzero] at h
    exact Prod.ext (congrArg Prod.fst h).symm
      (Prod.ext (neg_eq_zero.1 (congrArg (fun v : R × R × R => v.2.1) h).symm) (hz (0, 0, 1)))
  exact ⟨h₁, h₂, h₃⟩

end LinearMap

namespace TauCeti

namespace LinearMap

variable {R S E E' : Type*} [Semiring R] [CommSemiring S] [SMul R S] [AddCommMonoid E]
  [Module R E] [Module S E] [IsScalarTower R S E] [AddCommMonoid E'] [Module R E'] [Module S E']
  [IsScalarTower R S E']

/-- **Multiplication by a scalar on a product of modules is carried out blockwise.** Read as an
`R`-linear map, multiplication by `c : S` on `E × E'` is the `LinearMap.prodMap` of the
multiplications by `c` on the two factors. -/
theorem lsmul_restrictScalars_prodMap (c : S) :
    (LinearMap.lsmul S (E × E') c).restrictScalars R =
      LinearMap.prodMap ((LinearMap.lsmul S E c).restrictScalars R)
        ((LinearMap.lsmul S E' c).restrictScalars R) := by
  ext <;> simp

end LinearMap

end TauCeti
