/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Finiteness.Prod
public import TauCeti.Algebra.Module.Submodule.AddSubgroup

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
* `LinearEquiv.det_skewProd`: the same determinant formula for block triangular
  automorphisms, independently of the off-diagonal block.
* `LinearEquiv.nonempty_linearEquiv_of_isUnit_snd_comp_inr`: a linear equivalence `M × P ≃ N × P`
  whose lower-right block is invertible gives `M ≃ N`.
* `LinearMap.det_eq_det_mul_det_of_fst_apply_inr`: a block lower triangular endomorphism
  `(x, y) ↦ (a x, c x + d y)` of `M₁ × M₂` has determinant `det a * det d`, and
  `LinearMap.det_eq_det_snd_comp_comp_inr` is the case `a = id`.
* `LinearMap.finrank_graph`: the graph of a linear map `M → M₂` has the dimension of `M`.
* `LinearMap.graphAddSubgroup`, `LinearMap.graphAddCommGroup`, and `LinearMap.graphEquiv`:
  the `AddSubgroup` and `AddCommGroup` structure on the graph of a semiring-linear map between
  additive commutative groups, and the linear equivalence `M ≃ₗ[R] f.graph` with simp lemmas
  `LinearMap.coe_graphEquiv_apply` and `LinearMap.graphEquiv_symm_apply`.
* `LinearMap.isCompl_graph_ker_fst`: the graph of a linear map `M → M₂` is a complement of
  `0 × M₂`.
* `TauCeti.antidiagDiagEquiv`: when `2` is invertible, the linear automorphism
  `(x, y) ↦ (x, -x) + (y, y)` of `M × M`, carrying the two coordinate axes onto the antidiagonal
  `(-LinearMap.id).graph` and the diagonal `LinearMap.id.graph`.
* `TauCeti.isCompl_graph_neg_id_graph_id`: when `2` is invertible, `M × M` is the direct sum of
  the antidiagonal and the diagonal.
* `TauCeti.linearMap_ext_antidiag_diag`, `TauCeti.linearMap_ext₂_antidiag_diag`: a semilinear map,
  respectively a sesquilinear form, on `M × M` is determined by its values on the antidiagonal and
  the diagonal.
* `LinearMap.coprod_comp_prodComm`: precomposing `f.coprod g` with the exchange of factors gives
  `g.coprod f`, the linear version of `ContinuousLinearMap.coprod_comp_prodComm`.
* `LinearMap.surjective_coprod_iff`, `LinearMap.surjective_coprod_neg_iff`: `f.coprod g` and
  `f.coprod (-g)` are surjective if and only if `range f ⊔ range g = ⊤`.
* `LinearMap.coprod_neg_comp_prodComm`, `LinearMap.map_prodComm_ker_coprod_neg`,
  `LinearMap.surjective_coprod_neg_comm`: the exchange of factors negates `(ξ, η) ↦ α ξ - β η`,
  identifies the fibre product `{(ξ, η) | α ξ = β η}` of `α` and `β` with that of `β`
  and `α`, and transversality, the surjectivity of `(ξ, η) ↦ α ξ - β η`, is symmetric.
* `LinearMap.fiberProductAssoc`: the reassociation `(X ×_T Y) ×_S Z ≃ X ×_T (Y ×_S Z)` of iterated
  fibre products of linear maps, with its components `LinearMap.fiberProductAssoc_apply_fst`,
  `LinearMap.fiberProductAssoc_apply_snd` and those of its inverse
  `LinearMap.fiberProductAssoc_symm_apply_fst`, `LinearMap.fiberProductAssoc_symm_apply_snd`.
* `LinearMap.injective_prodMap`, `LinearMap.surjective_prodMap`: a product of injective, resp.
  surjective, linear maps is injective, resp. surjective, stated for the coercion of
  `f.prodMap g`.
* `LinearMap.surjective_of_surjective_prod_right`: the second component of a surjective map
  `(f, g)` to a product is surjective.
* `LinearMap.prodMap_comp_append`: `f.prodMap g` sends an appended family of vectors of the two
  factors to the appended family of their images.
* `LinearMap.prodMap_comp_inl`, `LinearMap.snd_comp_prodMap`: the commuting squares of the split
  rows `0 → M₁ → M₁ × M₂ → M₂ → 0` and `0 → M₃ → M₃ × M₄ → M₄ → 0` with vertical maps `f`,
  `f.prodMap g` and `g`.
* `LinearMap.kerProdMapEquiv`: the kernel of `f.prodMap g` is `ker f × ker g`.
* `LinearMap.finite_ker_prodMap`, `LinearMap.finrank_ker_prodMap`: the kernel of `f.prodMap g` is
  finite when those of `f` and `g` are, with the summed rank.
* `LinearMap.surjective_coprod_of_comp_left`, `LinearMap.surjective_coprod_of_comp_right`,
  `LinearMap.surjective_coprod_neg_of_comp_right`: surjectivity of `f.coprod g` survives
  removing a precomposition from either map. In particular transversality passes from `α ∘ h`
  and `β`, or from `α` and `β ∘ h`, to `α` and `β`.
* `LinearMap.injective_domRestrict_of_injective_prod`,
  `LinearMap.bijective_domRestrict_of_bijective_prod`: when the augmented map `f.prod g` is
  injective or bijective, `g` is injective or bijective on the kernel of `f`.
  Consequently the kernel of `f` is finite when the target of `g` is Noetherian
  (`LinearMap.finite_ker_of_injective_prod`), and the cokernel of `f` is zero
  (`LinearMap.subsingleton_quotient_range_of_surjective_prod`).
* `LinearMap.surjective_coprod_neg_assoc_outer` and its converse
  `LinearMap.surjective_coprod_neg_assoc_symm_outer`: transversality of one bracketing of an
  iterated fibre product gives transversality of the outer fibre product of the other; the inner
  ones follow from the previous item.
* `LinearMap.fiberProductInclusionLeft`, `LinearMap.fiberProductInclusionRight`: for a subspace
  of one factor, the inclusion of the smaller fibre product in the fibre product of `α` and `β`.
* `LinearMap.kerEquivKerIdProdMap`: the kernel of `g` is the kernel of `id × g`, embedded in the
  second factor.
* `LinearMap.axes_of_commute_neg_snd`: a linear endomorphism of `R × R × R` preserving the third
  coordinate and commuting with `(x, y, z) ↦ (x, -y, 0)` preserves the first two coordinate axes
  and fixes the third basis vector.
* `TauCeti.LinearMap.lsmul_restrictScalars_prodMap`: multiplication by a scalar on a product of
  modules, read over the base of a scalar tower, is the product map of the two multiplications.
-/

public section

namespace LinearMap

section CommRing

variable {R M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂]
  [Module R M₂] [Module.Free R M₁] [Module.Finite R M₁] [Module.Free R M₂] [Module.Finite R M₂]

/-- **The determinant of a block lower triangular map.** An endomorphism `g` of `M₁ × M₂` that
maps `0 × M₂` into itself, `g (x, y) = (a x, c x + d y)`, has determinant `det a * det d`, where
`a = fst ∘ g ∘ inl` and `d = snd ∘ g ∘ inr` are its diagonal blocks, independently of the
off-diagonal block `c`. -/
theorem det_eq_det_mul_det_of_fst_apply_inr {g : Module.End R (M₁ × M₂)}
    (hg : ∀ y, (g (0, y)).1 = 0) :
    LinearMap.det g = LinearMap.det (fst R M₁ M₂ ∘ₗ g ∘ₗ inl R M₁ M₂) *
      LinearMap.det (snd R M₁ M₂ ∘ₗ g ∘ₗ inr R M₁ M₂) := by
  classical
  let b₁ := Module.Free.chooseBasis R M₁
  let b₂ := Module.Free.chooseBasis R M₂
  have hmat : LinearMap.toMatrix (b₁.prod b₂) (b₁.prod b₂) g =
      Matrix.fromBlocks (LinearMap.toMatrix b₁ b₁ (fst R M₁ M₂ ∘ₗ g ∘ₗ inl R M₁ M₂)) 0
        (LinearMap.toMatrix b₁ b₂ (snd R M₁ M₂ ∘ₗ g ∘ₗ inl R M₁ M₂))
        (LinearMap.toMatrix b₂ b₂ (snd R M₁ M₂ ∘ₗ g ∘ₗ inr R M₁ M₂)) := by
    ext (i | i) (j | j) <;> simp [LinearMap.toMatrix_apply, hg]
  rw [← LinearMap.det_toMatrix (b₁.prod b₂), hmat, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

/-- An endomorphism `(x, y) ↦ (x, c x + d y)` of `M₁ × M₂`, whose first component is the first
projection, has the determinant of its lower-right block `d = snd ∘ g ∘ inr`. -/
theorem det_eq_det_snd_comp_comp_inr {g : Module.End R (M₁ × M₂)}
    (hg : ∀ z, (g z).1 = z.1) :
    LinearMap.det g = LinearMap.det (snd R M₁ M₂ ∘ₗ g ∘ₗ inr R M₁ M₂) := by
  rw [det_eq_det_mul_det_of_fst_apply_inr fun y ↦ hg (0, y)]
  have : fst R M₁ M₂ ∘ₗ g ∘ₗ inl R M₁ M₂ = LinearMap.id := LinearMap.ext fun x ↦ hg (x, 0)
  rw [this, LinearMap.det_id, one_mul]

end CommRing

end LinearMap

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
  apply Units.ext
  simp only [coe_det, Units.val_mul]
  rw [LinearMap.det_eq_det_mul_det_of_fst_apply_inr fun y ↦ by simp [LinearEquiv.skewProd_apply]]
  exact congrArg₂ (· * ·)
    (congrArg _ (LinearMap.ext fun x ↦ by simp [LinearEquiv.skewProd_apply]))
    (congrArg _ (LinearMap.ext fun x ↦ by simp [LinearEquiv.skewProd_apply]))

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

/-- The graph of a semiring-linear map between additive commutative groups is closed under
negation. -/
theorem graph_neg_mem {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (f : E →ₗ[R] F) :
    ∀ p ∈ f.graph, -p ∈ f.graph := fun p hp ↦
  (mem_graph_iff f (-p)).mpr <| by
    rw [Prod.snd_neg, Prod.fst_neg, map_neg, (mem_graph_iff f p).mp hp]

/-- The graph of a semiring-linear map between additive commutative groups as an `AddSubgroup`. -/
@[expose]
def graphAddSubgroup {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (f : E →ₗ[R] F) : AddSubgroup (E × F) :=
  f.graph.toAddSubgroupOfNegMem f.graph_neg_mem

@[simp]
theorem coe_graphAddSubgroup {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (f : E →ₗ[R] F) :
    (f.graphAddSubgroup : Set (E × F)) = f.graph :=
  rfl

@[simp]
theorem mem_graphAddSubgroup {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (f : E →ₗ[R] F) {p : E × F} :
    p ∈ f.graphAddSubgroup ↔ p ∈ f.graph :=
  Iff.rfl

/-- The graph of a semiring-linear map between additive commutative groups inherits an
`AddCommGroup` structure. -/
@[expose, instance_reducible]
def graphAddCommGroup {R E F : Type*} [Semiring R] [AddCommGroup E] [Module R E]
    [AddCommGroup F] [Module R F] (f : E →ₗ[R] F) : AddCommGroup f.graph :=
  f.graph.addCommGroupOfNegMem f.graph_neg_mem

/-- A linear map over a semiring induces a linear equivalence between its domain and its graph. -/
@[expose]
def graphEquiv {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] (f : E →ₗ[R] F) : E ≃ₗ[R] f.graph :=
  (LinearEquiv.ofLeftInverse (f := LinearMap.id.prod f) (g := Prod.fst) fun _ ↦ rfl).trans
    (LinearEquiv.ofEq _ _ f.graph_eq_range_prod.symm)

@[simp]
theorem coe_graphEquiv_apply {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] (f : E →ₗ[R] F) (x : E) :
    (f.graphEquiv x : E × F) = (x, f x) :=
  rfl

@[simp]
theorem graphEquiv_symm_apply {R E F : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [AddCommMonoid F] [Module R F] (f : E →ₗ[R] F) (p : f.graph) :
    f.graphEquiv.symm p = (p : E × F).1 :=
  rfl

/-- The graph of a linear map `f : M → M₂` is a complement of the kernel `0 × M₂` of the first
projection: every `(x, y)` splits uniquely as `(x, f x) + (0, y - f x)`. -/
theorem isCompl_graph_ker_fst {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M₂] [Module R M₂] (f : M →ₗ[R] M₂) : IsCompl (graph f) (ker (fst R M M₂)) := by
  refine ⟨Submodule.disjoint_def.2 fun ⟨x, y⟩ hg hk ↦ ?_, codisjoint_iff.2 <| eq_top_iff.2
    fun ⟨x, y⟩ _ ↦ ?_⟩
  · simp only [mem_graph_iff, mem_ker, fst_apply] at hg hk
    simp [hk, hg]
  · have hxy : ((x, y) : M × M₂) = (x, f x) + (0, y - f x) := by simp
    rw [hxy]
    exact Submodule.add_mem_sup ((mem_graph_iff _ _).2 rfl) (by simp)

/-- A product map `f × g` carries the graph of `φ` onto the graph of `ψ` when `f` is surjective
and `g ∘ φ = ψ ∘ f`. For instance a surjective `f` acting diagonally, as `f × f`, carries the
diagonal `LinearMap.id.graph` onto the diagonal and the antidiagonal `(-LinearMap.id).graph` onto
the antidiagonal. -/
theorem map_prodMap_graph {R M₁ M₂ M₃ M₄ : Type*} [Semiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃] [AddCommMonoid M₄]
    [Module R M₄] {f : M₁ →ₗ[R] M₃} {g : M₂ →ₗ[R] M₄} {φ : M₁ →ₗ[R] M₂} {ψ : M₃ →ₗ[R] M₄}
    (hf : Function.Surjective f) (h : g ∘ₗ φ = ψ ∘ₗ f) :
    (graph φ).map (f.prodMap g) = graph ψ := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_map, mem_graph_iff, prodMap_apply, Prod.exists, Prod.mk.injEq]
  refine ⟨?_, fun hb ↦ ?_⟩
  · rintro ⟨x, y, rfl, rfl, rfl⟩
    exact LinearMap.congr_fun h x
  · obtain ⟨x, rfl⟩ := hf a
    exact ⟨x, φ x, rfl, rfl, (LinearMap.congr_fun h x).trans hb.symm⟩

end LinearMap

/-! ### The antidiagonal and the diagonal of `M × M` -/

namespace TauCeti

open LinearMap Submodule

variable (R M : Type*) [CommRing R] [Invertible (2 : R)] [AddCommGroup M] [Module R M]

/-- When `2` is invertible, the linear automorphism of `M × M` sending `(x, y)` to
`(x, -x) + (y, y) = (x + y, y - x)`, that is, the first factor to the antidiagonal and the second
to the diagonal. Its inverse is `(u, v) ↦ ((u - v) / 2, (u + v) / 2)`. -/
def antidiagDiagEquiv : (M × M) ≃ₗ[R] M × M where
  toFun p := (p.1 + p.2, p.2 - p.1)
  invFun q := ((⅟2 : R) • (q.1 - q.2), (⅟2 : R) • (q.1 + q.2))
  map_add' p q := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
  map_smul' c p := by
    ext <;> simp [smul_add, smul_sub]
  left_inv p := by
    ext <;> dsimp only
    · rw [show p.1 + p.2 - (p.2 - p.1) = (2 : R) • p.1 by module, invOf_smul_smul]
    · rw [show p.1 + p.2 + (p.2 - p.1) = (2 : R) • p.2 by module, invOf_smul_smul]
  right_inv q := by
    ext <;> dsimp only
    · rw [← smul_add, show q.1 - q.2 + (q.1 + q.2) = (2 : R) • q.1 by module, invOf_smul_smul]
    · rw [← smul_sub, show q.1 + q.2 - (q.1 - q.2) = (2 : R) • q.2 by module, invOf_smul_smul]

variable {R M}

/-- The automorphism `antidiagDiagEquiv` sends `(x, y)` to `(x + y, y - x)`. -/
@[simp]
theorem antidiagDiagEquiv_apply (p : M × M) :
    antidiagDiagEquiv R M p = (p.1 + p.2, p.2 - p.1) := (rfl)

/-- The inverse of `antidiagDiagEquiv` sends `(u, v)` to `((u - v) / 2, (u + v) / 2)`. -/
@[simp]
theorem antidiagDiagEquiv_symm_apply (q : M × M) :
    (antidiagDiagEquiv R M).symm q =
      ((⅟2 : R) • (q.1 - q.2), (⅟2 : R) • (q.1 + q.2)) := (rfl)

/-- The automorphism `antidiagDiagEquiv` decomposes a vector as an antidiagonal plus a diagonal
vector. -/
theorem antidiagDiagEquiv_apply_eq_add (x y : M) :
    antidiagDiagEquiv R M (x, y) = (x, -x) + (y, y) := by
  ext <;> simp [sub_eq_neg_add]

/-- The automorphism `antidiagDiagEquiv` carries the first axis `M × 0` onto the antidiagonal. -/
theorem map_antidiagDiagEquiv_range_inl :
    (range (inl R M M)).map (antidiagDiagEquiv R M : (M × M) →ₗ[R] M × M) =
      (-LinearMap.id : M →ₗ[R] M).graph := by
  ext ⟨a, b⟩
  simp only [mem_map, mem_range, inl_apply, mem_graph_iff, LinearMap.neg_apply, id_apply]
  refine ⟨?_, fun h ↦ ⟨(a, 0), ⟨a, rfl⟩, by simp [h]⟩⟩
  rintro ⟨_, ⟨x, rfl⟩, h⟩
  simp only [LinearEquiv.coe_coe, antidiagDiagEquiv_apply, add_zero, zero_sub,
    Prod.mk.injEq] at h
  rw [← h.1, ← h.2]

/-- The automorphism `antidiagDiagEquiv` carries the second axis `0 × M` onto the diagonal. -/
theorem map_antidiagDiagEquiv_range_inr :
    (range (inr R M M)).map (antidiagDiagEquiv R M : (M × M) →ₗ[R] M × M) =
      (LinearMap.id : M →ₗ[R] M).graph := by
  ext ⟨a, b⟩
  simp only [mem_map, mem_range, inr_apply, mem_graph_iff, id_apply]
  refine ⟨?_, fun h ↦ ⟨(0, a), ⟨a, rfl⟩, by simp [h]⟩⟩
  rintro ⟨_, ⟨x, rfl⟩, h⟩
  simp only [LinearEquiv.coe_coe, antidiagDiagEquiv_apply, zero_add, sub_zero,
    Prod.mk.injEq] at h
  rw [← h.1, ← h.2]

/-- When `2` is invertible, `M × M` is the direct sum of the antidiagonal and the diagonal. -/
theorem isCompl_graph_neg_id_graph_id :
    IsCompl (-LinearMap.id : M →ₗ[R] M).graph (LinearMap.id : M →ₗ[R] M).graph := by
  rw [← map_antidiagDiagEquiv_range_inl, ← map_antidiagDiagEquiv_range_inr]
  exact (orderIsoMapComap (antidiagDiagEquiv R M)).isCompl_iff.1 isCompl_range_inl_inr

/-- The automorphism `antidiagDiagEquiv` commutes with any linear map acting diagonally. -/
theorem antidiagDiagEquiv_prodMap {M' : Type*} [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (p : M × M) :
    antidiagDiagEquiv R M' (f.prodMap f p) =
      f.prodMap f (antidiagDiagEquiv R M p) := by
  simp

/-- A semilinear map on `M × M` is determined by its values on the antidiagonal and on the
diagonal. -/
theorem linearMap_ext_antidiag_diag {S P : Type*} [Semiring S] [AddCommMonoid P] [Module S P]
    {σ : R →+* S} {f g : M × M →ₛₗ[σ] P} (hA : ∀ x, f (x, -x) = g (x, -x))
    (hD : ∀ x, f (x, x) = g (x, x)) : f = g :=
  ext_on_codisjoint isCompl_graph_neg_id_graph_id.codisjoint
    (fun ⟨x, y⟩ hp ↦ by rw [show y = -x by simpa using hp]; exact hA x)
    fun ⟨x, y⟩ hp ↦ by rw [show y = x by simpa using hp]; exact hD x

/-- A sesquilinear form on `M × M` is determined by its four blocks with respect to the
antidiagonal and the diagonal. -/
theorem linearMap_ext₂_antidiag_diag {N : Type*} [AddCommGroup N] [Module R N] {I₁ I₂ : R →+* R}
    {C C' : M × M →ₛₗ[I₁] M × M →ₛₗ[I₂] N}
    (hAA : ∀ x y, C (x, -x) (y, -y) = C' (x, -x) (y, -y))
    (hAD : ∀ x y, C (x, -x) (y, y) = C' (x, -x) (y, y))
    (hDA : ∀ x y, C (x, x) (y, -y) = C' (x, x) (y, -y))
    (hDD : ∀ x y, C (x, x) (y, y) = C' (x, x) (y, y)) : C = C' :=
  linearMap_ext_antidiag_diag (fun x ↦ linearMap_ext_antidiag_diag (hAA x) (hAD x))
    fun x ↦ linearMap_ext_antidiag_diag (hDA x) (hDD x)

end TauCeti

namespace LinearMap

section Semiring

variable {R M₁ M₂ M₃ : Type*} [Semiring R] [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂]
  [Module R M₂] [AddCommMonoid M₃] [Module R M₃]

/-- Precomposing a map on a product with the exchange of the factors exchanges its components. -/
theorem coprod_comp_prodComm (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
    f.coprod g ∘ₗ (LinearEquiv.prodComm R M₂ M₁).toLinearMap = g.coprod f := by
  ext <;> simp

/-- The coproduct `(x, y) ↦ f x + g y` of two linear maps is surjective if and only if their ranges
together span the codomain. -/
theorem surjective_coprod_iff (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
    Function.Surjective (f.coprod g) ↔ range f ⊔ range g = ⊤ := by
  rw [← range_eq_top, range_coprod]

variable {M₄ : Type*} [AddCommMonoid M₄] [Module R M₄]

/-- A product of injective linear maps is injective, stated for the coercion of `f.prodMap g`. -/
theorem injective_prodMap {f : M₁ →ₗ[R] M₃} {g : M₂ →ₗ[R] M₄} (hf : Function.Injective f)
    (hg : Function.Injective g) : Function.Injective (f.prodMap g) :=
  hf.prodMap hg

/-- A product of surjective linear maps is surjective, stated for the coercion of
`f.prodMap g`. -/
theorem surjective_prodMap {f : M₁ →ₗ[R] M₃} {g : M₂ →ₗ[R] M₄} (hf : Function.Surjective f)
    (hg : Function.Surjective g) : Function.Surjective (f.prodMap g) :=
  hf.prodMap hg

/-- If `(f, g) : M₁ → M₂ × M₃` is surjective, then so is its second component `g`. -/
theorem surjective_of_surjective_prod_right {f : M₁ →ₗ[R] M₂} {g : M₁ →ₗ[R] M₃}
    (h : Function.Surjective (f.prod g)) : Function.Surjective g :=
  -- `g` is `snd ∘ₗ f.prod g` by definition (`LinearMap.snd_prod` is proved by `rfl`).
  Prod.snd_surjective.comp h

/-- The product map `f × g` sends an appended family of vectors of the two factors to the appended
family of their images. -/
theorem prodMap_comp_append (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) {m n : ℕ} (p : Fin m → M₁)
    (q : Fin n → M₂) :
    ⇑(f.prodMap g) ∘ Fin.append (inl R M₁ M₂ ∘ p) (inr R M₁ M₂ ∘ q) =
      Fin.append (inl R M₃ M₄ ∘ f ∘ p) (inr R M₃ M₄ ∘ g ∘ q) := by
  funext i
  induction i using Fin.addCases <;> simp

/-- The left square of the split rows `0 → M₁ → M₁ × M₂ → M₂ → 0` and
`0 → M₃ → M₃ × M₄ → M₄ → 0` with vertical maps `f`, `f.prodMap g` and `g` commutes. -/
theorem prodMap_comp_inl (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) :
    f.prodMap g ∘ₗ inl R M₁ M₂ = inl R M₃ M₄ ∘ₗ f := by
  ext <;> simp

/-- The right square of the split rows `0 → M₁ → M₁ × M₂ → M₂ → 0` and
`0 → M₃ → M₃ × M₄ → M₄ → 0` with vertical maps `f`, `f.prodMap g` and `g` commutes. -/
theorem snd_comp_prodMap (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄) :
    snd R M₃ M₄ ∘ₗ f.prodMap g = g ∘ₗ snd R M₁ M₂ := by
  ext <;> simp
variable (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₄)

/-- The kernel of `f.prodMap g` is `ker f × ker g`. -/
def kerProdMapEquiv : ker (f.prodMap g) ≃ₗ[R] ker f × ker g :=
  (LinearEquiv.ofEq _ _ (ker_prodMap f g)).trans (Submodule.prodEquiv _ _)

@[simp]
theorem coe_kerProdMapEquiv_apply_fst (x : ker (f.prodMap g)) :
    ((kerProdMapEquiv f g x).1 : M₁) = (x : M₁ × M₂).1 :=
  (rfl)

@[simp]
theorem coe_kerProdMapEquiv_apply_snd (x : ker (f.prodMap g)) :
    ((kerProdMapEquiv f g x).2 : M₂) = (x : M₁ × M₂).2 :=
  (rfl)

@[simp]
theorem coe_kerProdMapEquiv_symm_apply (x : ker f × ker g) :
    ((kerProdMapEquiv f g).symm x : M₁ × M₂) = ((x.1 : M₁), (x.2 : M₂)) :=
  (rfl)

variable {f g} in
/-- The kernel of `f.prodMap g` is `ker f × ker g`, so it is finite when they are. -/
instance finite_ker_prodMap [Module.Finite R (ker f)] [Module.Finite R (ker g)] :
    Module.Finite R (ker (f.prodMap g)) :=
  .equiv (kerProdMapEquiv f g).symm

/-- The kernel of `f.prodMap g` has rank `finrank (ker f) + finrank (ker g)`. -/
@[simp]
theorem finrank_ker_prodMap [StrongRankCondition R] [Module.Free R (ker f)]
    [Module.Free R (ker g)] [Module.Finite R (ker f)] [Module.Finite R (ker g)] :
    Module.finrank R (ker (f.prodMap g)) = Module.finrank R (ker f) + Module.finrank R (ker g) := by
  rw [(kerProdMapEquiv f g).finrank_eq, Module.finrank_prod]

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

/-- If `f.prod g` is injective, `g` is injective on the kernel of `f`. -/
theorem injective_domRestrict_of_injective_prod {f : M₁ →ₗ[R] M₂} {g : M₁ →ₗ[R] M₃}
    (h : Function.Injective (f.prod g)) : Function.Injective (g.domRestrict (ker f)) :=
  fun x y hxy ↦ Subtype.ext (h (Prod.ext ((mem_ker.mp x.property).trans
      (mem_ker.mp y.property).symm) hxy))

/-- If `f.prod g` is bijective, `g` maps the kernel of `f` bijectively onto its target. -/
theorem bijective_domRestrict_of_bijective_prod {f : M₁ →ₗ[R] M₂} {g : M₁ →ₗ[R] M₃}
    (h : Function.Bijective (f.prod g)) : Function.Bijective (g.domRestrict (ker f)) :=
  ⟨injective_domRestrict_of_injective_prod h.1, fun v ↦
    let ⟨m, hm⟩ := h.2 (0, v)
    ⟨⟨m, congrArg Prod.fst hm⟩, congrArg Prod.snd hm⟩⟩

/-- If `f.prod g` is injective and the target of `g` is Noetherian, the kernel of `f` is finite. -/
theorem finite_ker_of_injective_prod [IsNoetherian R M₃] {f : M₁ →ₗ[R] M₂} {g : M₁ →ₗ[R] M₃}
    (h : Function.Injective (f.prod g)) : Module.Finite R (ker f) :=
  Module.Finite.of_injective _ (injective_domRestrict_of_injective_prod h)

end Semiring

/-- The difference coproduct `(x, y) ↦ f x - g y` of two linear maps is surjective if and only if
their ranges together span the codomain. -/
theorem surjective_coprod_neg_iff {R M₁ M₂ M₃ : Type*} [Ring R]
    [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₃) (g : M₂ →ₗ[R] M₃) :
    Function.Surjective (f.coprod (-g)) ↔ range f ⊔ range g = ⊤ := by
  rw [surjective_coprod_iff, range_neg]

/-- If `f.prod g` is onto, the cokernel of `f` is zero. -/
theorem subsingleton_quotient_range_of_surjective_prod {R M₁ M₂ M₃ : Type*} [Ring R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃]
    [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₁ →ₗ[R] M₃} (h : Function.Surjective (f.prod g)) :
    Subsingleton (M₂ ⧸ range f) :=
  -- `f` is `fst ∘ₗ f.prod g` by definition (`LinearMap.fst_prod` is proved by `rfl`).
  Submodule.Quotient.subsingleton_iff.mpr (range_eq_top.mpr (Prod.fst_surjective.comp h))

section KerProdMap

variable {R L M N : Type*} [Semiring R] [AddCommMonoid L] [Module R L] [AddCommMonoid M]
  [Module R M] [AddCommMonoid N] [Module R N]

variable (L) in
/-- The kernel of `id × g : L × M → L × N` is the kernel of `g`, embedded in the second factor. -/
def kerEquivKerIdProdMap (g : M →ₗ[R] N) :
    ker g ≃ₗ[R] ker ((LinearMap.id : L →ₗ[R] L).prodMap g) where
  toFun x := ⟨(0, x), by simp⟩
  invFun y := ⟨y.val.2, (Prod.mk_eq_zero.1 (mem_ker.1 y.property)).2⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  left_inv _ := rfl
  right_inv y := Subtype.ext (Prod.ext (Prod.mk_eq_zero.1 (mem_ker.1 y.property)).1.symm rfl)

@[simp]
theorem coe_kerEquivKerIdProdMap_apply (g : M →ₗ[R] N) (x : ker g) :
    (kerEquivKerIdProdMap L g x : L × M) = (0, (x : M)) :=
  (rfl)

@[simp]
theorem coe_kerEquivKerIdProdMap_symm_apply (g : M →ₗ[R] N)
    (y : ker ((LinearMap.id : L →ₗ[R] L).prodMap g)) :
    ((kerEquivKerIdProdMap L g).symm y : M) = (y : L × M).2 :=
  (rfl)

end KerProdMap

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
  toFun r := ⟨(r.val.1.val.1, ⟨(r.val.1.val.2, r.val.2),
      by simpa [-map_coe_ker] using mem_ker.1 r.property⟩),
    by simpa [-map_coe_ker] using mem_ker.1 r.val.1.property⟩
  invFun r := ⟨(⟨(r.val.1, r.val.2.val.1),
      by simpa [-map_coe_ker] using mem_ker.1 r.property⟩, r.val.2.val.2),
    by simpa [-map_coe_ker] using mem_ker.1 r.val.2.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {α β γ δ}

/-- The `X`-component of the reassociation of `((ξ, η), ζ)` is `ξ`. -/
@[simp]
theorem fiberProductAssoc_apply_fst
    (r : ker ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ))) :
    (fiberProductAssoc α β γ δ r).val.1 = r.val.1.val.1 :=
 (rfl)

/-- The `Y ×_S Z`-component of the reassociation of `((ξ, η), ζ)` is `(η, ζ)`. -/
@[simp]
theorem fiberProductAssoc_apply_snd
    (r : ker ((γ ∘ₗ snd R X Y ∘ₗ (ker (α.coprod (-β))).subtype).coprod (-δ))) :
    ((fiberProductAssoc α β γ δ r).val.2 : Y × Z) = (r.val.1.val.2, r.val.2) :=
 (rfl)

/-- The `X ×_T Y`-component of the inverse reassociation of `(ξ, (η, ζ))` is `(ξ, η)`. -/
@[simp]
theorem fiberProductAssoc_symm_apply_fst
    (r : ker (α.coprod (-(β ∘ₗ fst R Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype)))) :
    (((fiberProductAssoc α β γ δ).symm r).val.1 : X × Y) = (r.val.1, r.val.2.val.1) :=
 (rfl)

/-- The `Z`-component of the inverse reassociation of `(ξ, (η, ζ))` is `ζ`. -/
@[simp]
theorem fiberProductAssoc_symm_apply_snd
    (r : ker (α.coprod (-(β ∘ₗ fst R Y Z ∘ₗ (ker (γ.coprod (-δ))).subtype)))) :
    ((fiberProductAssoc α β γ δ).symm r).val.2 = r.val.2.val.2 :=
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
    exact (z : p × Y).1.property
  · have hv := mem_ker.1 v.property
    rw [coprod_apply] at hv
    simpa using hv

/-- A point of the fibre product of `α` and `β` lies in `X ×_T p` exactly when its second
component lies in `p`. -/
theorem mem_range_fiberProductInclusionRight {p : Submodule R Y} {v : ker (α.coprod (-β))} :
    v ∈ range (fiberProductInclusionRight α β p) ↔ (v : X × Y).2 ∈ p := by
  refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun h ↦ ⟨⟨((v : X × Y).1, ⟨_, h⟩), ?_⟩, Subtype.ext (by simp)⟩⟩
  · rw [← hz, coe_fiberProductInclusionRight_apply]
    exact (z : X × p).2.property
  · have hv := mem_ker.1 v.property
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
