/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.RingTheory.Etale.PiTensorProduct
public import TauCeti.RingTheory.PiTensorProduct.Equiv
public import TauCeti.RingTheory.Unramified.Diagonal
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import TauCeti.Algebra.TensorProduct.Maps
import TauCeti.RingTheory.Etale.Idempotent

/-!
# The frame algebra of ordered tuples of distinct points

Let `S` be an essentially finite type, formally unramified `R`-algebra and `ι` a finite type.
The diagonal of `Spec S` is open and closed in `Spec (S ⊗[R] S)`, cut out by Mathlib's idempotent
`Algebra.FormallyUnramified.elem R S`. Pulling it back along the projection to the factors `i`
and `j` of the tensor power `⨂[R] _ : ι, S` gives an idempotent `δᵢⱼ`
(`TauCeti.Algebra.tensorPowDiagonal`) cutting out the locus where the points `i` and `j` agree.
The product `ε = ∏_{i ≠ j} (1 - δᵢⱼ)` (`TauCeti.Algebra.distinctIdempotent`) cuts out the open
and closed locus of `ι`-tuples of pairwise distinct points, and the *frame algebra*

  `TauCeti.Algebra.FrameAlgebra R S ι = (⨂[R] _ : ι, S) ⧸ (1 - ε) ≅ ε · (⨂[R] _ : ι, S)`

is its ring of functions. The permutations of `ι` act on it by permuting the tensor factors.

For a split algebra `S = κ → R` the points are the elements of `κ`, and the frame algebra is the
algebra of functions on the embeddings `ι ↪ κ`, with `σ` acting by precomposition with `σ`
(`TauCeti.Algebra.FrameAlgebra.piEquiv`). For `κ = ι` it is the function algebra on `Perm ι`
with right translation, the trivial `Perm ι`-torsor (`TauCeti.Algebra.FrameAlgebra.permEquiv`).

For `S` finite étale of constant rank `n` and `ι = Fin n`, the frame algebra is the standard
candidate for a finite étale `Perm (Fin n)`-torsor over `R` splitting `S`, the ring-theoretic
Galois closure of `S`. A faithfully flat finite étale base change makes `S` split, and the
computation in this file is the split model of that torsor.

## Main definitions

* `TauCeti.Algebra.tensorPowDiagonal R S i j`: the idempotent `δᵢⱼ` of `⨂[R] _ : ι, S`.
* `TauCeti.Algebra.distinctIdempotent R S ι`: the idempotent `ε = ∏_{i ≠ j} (1 - δᵢⱼ)`.
* `TauCeti.Algebra.FrameAlgebra R S ι`: the frame algebra, with its action of `Equiv.Perm ι`.
* `TauCeti.Algebra.FrameAlgebra.piEquiv`, `TauCeti.Algebra.FrameAlgebra.permEquiv`: the frame
  algebra of a split algebra.

## Main results

* `TauCeti.Algebra.FrameAlgebra.mk_tensorPowDiagonal`: distinct slots carry distinct points.
* `TauCeti.Algebra.FrameAlgebra.lift`, `TauCeti.Algebra.FrameAlgebra.eq_lift_iff`: the universal
  property, algebra maps out of the tensor power separating every two distinct slots factor
  uniquely through the frame algebra.
* `TauCeti.Algebra.FrameAlgebra.smul_mk`: permutations act by permuting tensor factors.
* `TauCeti.Algebra.FrameAlgebra.etale`, `TauCeti.Algebra.FrameAlgebra.finite`: the frame algebra
  of a finite étale algebra is finite étale.
* `TauCeti.Algebra.FrameAlgebra.piEquiv_smul`, `TauCeti.Algebra.FrameAlgebra.permEquiv_smul`:
  equivariance of the split computation.

## References

* [Stacks Project, Tag 0BN2](https://stacks.math.columbia.edu/tag/0BN2), for the Galois closure
  of a connected object of a Galois category.
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 15.3.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra

open PiTensorProduct

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S]

section Diagonal

variable {ι : Type*} [DecidableEq ι]

/-- The idempotent `δᵢⱼ` of the tensor power `⨂[R] _ : ι, S` cutting out the locus where the
points in the slots `i` and `j` agree: the image of the diagonal idempotent
`Algebra.FormallyUnramified.elem R S` of `S ⊗[R] S` under the inclusion of the factors `i`
and `j`. -/
noncomputable def tensorPowDiagonal (i j : ι) : ⨂[R] _ : ι, S :=
  Algebra.TensorProduct.productMap (singleAlgHom (R := R) (A := fun _ : ι ↦ S) i)
    (singleAlgHom j) (Algebra.FormallyUnramified.elem R S)

variable {R S}

/-- An algebra map out of the tensor power sends `δᵢⱼ` to the image of the diagonal idempotent
under its restrictions to the slots `i` and `j`. -/
theorem map_tensorPowDiagonal {T : Type*} [CommSemiring T] [Algebra R T]
    (φ : (⨂[R] _ : ι, S) →ₐ[R] T) (i j : ι) :
    φ (tensorPowDiagonal R S i j) =
      Algebra.TensorProduct.productMap (φ.comp (singleAlgHom i)) (φ.comp (singleAlgHom j))
        (Algebra.FormallyUnramified.elem R S) := by
  rw [tensorPowDiagonal, ← AlgHom.comp_apply, AlgHom.comp_productMap]

/-- `δᵢⱼ` is idempotent, as the image of the diagonal idempotent. -/
theorem isIdempotentElem_tensorPowDiagonal (i j : ι) :
    IsIdempotentElem (tensorPowDiagonal R S i j) :=
  (Algebra.FormallyUnramified.isIdempotentElem_elem R S).map _

/-- A slot always carries the same point as itself. -/
@[simp]
theorem tensorPowDiagonal_self (i : ι) : tensorPowDiagonal R S i i = 1 := by
  have h : Algebra.TensorProduct.productMap (singleAlgHom (R := R) (A := fun _ : ι ↦ S) i)
      (singleAlgHom i) = (singleAlgHom i).comp (Algebra.TensorProduct.lmul' R) :=
    Algebra.TensorProduct.ext' fun a b ↦ by
      rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.comp_apply,
        Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
  rw [tensorPowDiagonal, h, AlgHom.comp_apply, Algebra.FormallyUnramified.lmul_elem, map_one]

/-- The slots `i` and `j` carry the same point exactly when `j` and `i` do. -/
theorem tensorPowDiagonal_comm (i j : ι) :
    tensorPowDiagonal R S i j = tensorPowDiagonal R S j i := by
  have h : (Algebra.TensorProduct.productMap (singleAlgHom (R := R) (A := fun _ : ι ↦ S) j)
      (singleAlgHom i)).comp (Algebra.TensorProduct.comm R S S).toAlgHom =
      Algebra.TensorProduct.productMap (singleAlgHom (A := fun _ : ι ↦ S) i) (singleAlgHom j) :=
    Algebra.TensorProduct.ext' fun a b ↦ by simp [mul_comm]
  rw [tensorPowDiagonal, tensorPowDiagonal, ← h, AlgHom.comp_apply]
  exact congrArg _ (FormallyUnramified.comm_elem R S)

/-- Permuting the tensor factors by `σ` moves `δᵢⱼ` to `δ_{σ i, σ j}`. -/
@[simp]
theorem permAlgEquiv_tensorPowDiagonal (σ : Equiv.Perm ι) (i j : ι) :
    permAlgEquiv S σ (tensorPowDiagonal R S i j) = tensorPowDiagonal R S (σ i) (σ j) := by
  rw [← AlgEquiv.coe_toAlgHom, map_tensorPowDiagonal]
  congr 2 <;> exact AlgHom.ext fun a ↦ permAlgEquiv_singleAlgHom σ _ a

end Diagonal

section Distinct

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The idempotent `ε = ∏_{i ≠ j} (1 - δᵢⱼ)` of the tensor power `⨂[R] _ : ι, S`, cutting out the
locus of `ι`-tuples of pairwise distinct points of `Spec S`. -/
noncomputable def distinctIdempotent : ⨂[R] _ : ι, S :=
  ∏ p ∈ (Finset.univ : Finset ι).offDiag, (1 - tensorPowDiagonal R S p.1 p.2)

variable {R S ι}

/-- `ε` is idempotent, as a product of idempotents. -/
theorem isIdempotentElem_distinctIdempotent :
    IsIdempotentElem (distinctIdempotent R S ι) :=
  Finset.prod_induction _ IsIdempotentElem (fun _ _ ↦ IsIdempotentElem.mul) .one
    fun p _ ↦ (isIdempotentElem_tensorPowDiagonal p.1 p.2).one_sub

/-- On tuples of pairwise distinct points, the points in two distinct slots differ. -/
theorem distinctIdempotent_mul_tensorPowDiagonal {i j : ι} (hij : i ≠ j) :
    distinctIdempotent R S ι * tensorPowDiagonal R S i j = 0 := by
  rw [distinctIdempotent, ← Finset.mul_prod_erase _ _ ((Finset.mem_offDiag (x := (i, j))).mpr
    ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩), mul_right_comm,
    (isIdempotentElem_tensorPowDiagonal i j).one_sub_mul_self, zero_mul]

/-- An algebra map out of the tensor power which separates every two distinct slots sends `ε`
to `1`. -/
theorem map_distinctIdempotent {T : Type*} [Semiring T] [Algebra R T]
    (φ : (⨂[R] _ : ι, S) →ₐ[R] T) (hφ : ∀ i j, i ≠ j → φ (tensorPowDiagonal R S i j) = 0) :
    φ (distinctIdempotent R S ι) = 1 :=
  Finset.prod_induction _ (fun x ↦ φ x = 1) (fun a b ha hb ↦ by rw [map_mul, ha, hb, mul_one])
    (map_one φ) fun p hp ↦ by
      have h := congrArg φ (sub_add_cancel 1 (tensorPowDiagonal R S p.1 p.2))
      rwa [map_add, hφ _ _ (Finset.mem_offDiag.mp hp).2.2, add_zero, map_one] at h

/-- Tuples indexed by a type with at most one element have no pairs of slots to separate. -/
@[simp]
theorem distinctIdempotent_of_subsingleton [Subsingleton ι] :
    distinctIdempotent R S ι = 1 := by
  exact Finset.prod_eq_one fun p hp ↦
    absurd (Subsingleton.elim p.1 p.2) (Finset.mem_offDiag.mp hp).2.2

/-- The locus of tuples of pairwise distinct points is stable under permuting the slots. -/
@[simp]
theorem permAlgEquiv_distinctIdempotent (σ : Equiv.Perm ι) :
    permAlgEquiv S σ (distinctIdempotent R S ι) = distinctIdempotent R S ι := by
  rw [distinctIdempotent, map_prod]
  refine Finset.prod_equiv (σ.prodCongr σ) (fun p ↦ ?_) fun p _ ↦ ?_
  · simp [Finset.mem_offDiag, σ.injective.ne_iff]
  · simp

end Distinct

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The *frame algebra* of `S` indexed by `ι`: the ring of functions on the open and closed
subscheme of `ι`-tuples of pairwise distinct points of `Spec S` in the `ι`-fold fibre power of
`Spec S` over `Spec R`. It is the quotient of `⨂[R] _ : ι, S` by `1 - ε`, the factor
`ε · (⨂[R] _ : ι, S)` cut out by `TauCeti.Algebra.distinctIdempotent`.

For `S` finite étale of constant rank `n` and `ι = Fin n` this is the standard construction of a
`Perm (Fin n)`-torsor splitting `S`, the ring-theoretic Galois closure of `S`; its split model is
`TauCeti.Algebra.FrameAlgebra.permEquiv`. -/
abbrev FrameAlgebra : Type _ :=
  (⨂[R] _ : ι, S) ⧸ Ideal.span {1 - distinctIdempotent R S ι}

namespace FrameAlgebra

variable {R S ι}

/-- In the frame algebra, the points in two distinct slots differ. -/
@[simp]
theorem mk_tensorPowDiagonal {i j : ι} (hij : i ≠ j) :
    Ideal.Quotient.mk (Ideal.span {1 - distinctIdempotent R S ι}) (tensorPowDiagonal R S i j) =
      0 := by
  refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton'.mpr
    ⟨tensorPowDiagonal R S i j, ?_⟩)
  rw [mul_sub, mul_one, mul_comm, distinctIdempotent_mul_tensorPowDiagonal hij, sub_zero]

/-- In the frame algebra, the idempotent cutting out the tuples of distinct points is `1`. -/
@[simp]
theorem mk_distinctIdempotent :
    Ideal.Quotient.mk (Ideal.span {1 - distinctIdempotent R S ι}) (distinctIdempotent R S ι) =
      1 := by
  rw [eq_comm, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _

section Lift

variable {T : Type*} [Semiring T] [Algebra R T]

/-- The universal property of the frame algebra: an algebra map out of the tensor power which
separates every two distinct slots, i.e. kills `δᵢⱼ` for `i ≠ j`, factors through the frame
algebra. -/
noncomputable def lift (φ : (⨂[R] _ : ι, S) →ₐ[R] T)
    (hφ : ∀ i j, i ≠ j → φ (tensorPowDiagonal R S i j) = 0) : FrameAlgebra R S ι →ₐ[R] T :=
  Ideal.Quotient.liftₐ _ φ fun x hx ↦ by
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, ← mul_one (φ (1 - _)), ← map_distinctIdempotent φ hφ, ← map_mul,
      isIdempotentElem_distinctIdempotent.one_sub_mul_self, map_zero, mul_zero]

/-- `TauCeti.Algebra.FrameAlgebra.lift φ hφ` sends the class of `x` to `φ x`. -/
@[simp]
theorem lift_mk (φ : (⨂[R] _ : ι, S) →ₐ[R] T)
    (hφ : ∀ i j, i ≠ j → φ (tensorPowDiagonal R S i j) = 0) (x : ⨂[R] _ : ι, S) :
    lift φ hφ (Ideal.Quotient.mk _ x) = φ x := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.lift φ hφ` restricts to `φ` along the quotient map. -/
@[simp]
theorem lift_comp_mkₐ (φ : (⨂[R] _ : ι, S) →ₐ[R] T)
    (hφ : ∀ i j, i ≠ j → φ (tensorPowDiagonal R S i j) = 0) :
    (lift φ hφ).comp (Ideal.Quotient.mkₐ R _) = φ :=
  Ideal.Quotient.liftₐ_comp ..

/-- `TauCeti.Algebra.FrameAlgebra.lift φ hφ` is the unique algebra map out of the frame algebra
restricting to `φ` along the quotient map. -/
theorem eq_lift_iff (φ : (⨂[R] _ : ι, S) →ₐ[R] T)
    (hφ : ∀ i j, i ≠ j → φ (tensorPowDiagonal R S i j) = 0) (ψ : FrameAlgebra R S ι →ₐ[R] T) :
    ψ = lift φ hφ ↔ ψ.comp (Ideal.Quotient.mkₐ R _) = φ :=
  ⟨fun h ↦ h ▸ lift_comp_mkₐ φ hφ,
    fun h ↦ Ideal.Quotient.algHom_ext R (h.trans (lift_comp_mkₐ φ hφ).symm)⟩

/-- Every algebra map out of the frame algebra is the lift of its restriction to the tensor
power. -/
@[simp]
theorem lift_comp_mkₐ_self (ψ : FrameAlgebra R S ι →ₐ[R] T) :
    lift (ψ.comp (Ideal.Quotient.mkₐ R _)) (fun i j hij ↦ by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, mk_tensorPowDiagonal hij, map_zero]) = ψ :=
  ((eq_lift_iff _ _ ψ).mpr rfl).symm

end Lift

variable (R S ι) in
/-- The permutations of `ι` act on the frame algebra by permuting the tensor factors. -/
noncomputable def permAlgEquiv : Equiv.Perm ι →* FrameAlgebra R S ι ≃ₐ[R] FrameAlgebra R S ι where
  toFun σ := Ideal.quotientEquivAlg _ _ (PiTensorProduct.permAlgEquiv S σ) <| by
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, map_sub, map_one,
      permAlgEquiv_distinctIdempotent]
  map_one' := AlgEquiv.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  map_mul' σ τ := AlgEquiv.ext fun x ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp

/-- The permutations of `ι` act on the frame algebra by `R`-algebra automorphisms, permuting the
tensor factors. -/
noncomputable instance : MulSemiringAction (Equiv.Perm ι) (FrameAlgebra R S ι) :=
  MulSemiringAction.compHom _ (permAlgEquiv R S ι)

/-- A permutation acts on the frame algebra through `TauCeti.Algebra.FrameAlgebra.permAlgEquiv`. -/
theorem smul_def (σ : Equiv.Perm ι) (x : FrameAlgebra R S ι) :
    σ • x = permAlgEquiv R S ι σ x := (rfl)

/-- A permutation `σ` acts on the class of `x` through the permutation of the tensor factors. -/
@[simp]
theorem smul_mk (σ : Equiv.Perm ι) (x : ⨂[R] _ : ι, S) :
    σ • Ideal.Quotient.mk (Ideal.span {1 - distinctIdempotent R S ι}) x =
      Ideal.Quotient.mk _ (PiTensorProduct.permAlgEquiv S σ x) := by
  rw [smul_def]
  exact Ideal.quotientEquivAlg_mk ..

/-- Permutations act on the frame algebra `R`-linearly. -/
instance : SMulCommClass (Equiv.Perm ι) R (FrameAlgebra R S ι) where
  smul_comm σ r x := by simp only [smul_def, map_smul]

/-- The frame algebra of an étale algebra is étale. -/
instance etale [Algebra.Etale R S] : Algebra.Etale R (FrameAlgebra R S ι) :=
  Etale.quotient_span_singleton isIdempotentElem_distinctIdempotent.one_sub

/-- The frame algebra of a finite algebra is finite. -/
instance finite [Module.Finite R S] : Module.Finite R (FrameAlgebra R S ι) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ R _).toLinearMap Ideal.Quotient.mk_surjective

end FrameAlgebra

section Split

variable {κ : Type*} [Finite κ]

variable {R ι}

/-- In the tensor power of the split algebra `κ → R`, viewed as functions on `ι → κ`, the
idempotent `δᵢⱼ` is the indicator of the maps `p` with `p i = p j`. -/
theorem piScalarAlgEquiv_tensorPowDiagonal [DecidableEq κ] (i j : ι) :
    piScalarAlgEquiv R (fun _ : ι ↦ κ) (tensorPowDiagonal R (κ → R) i j) =
      fun p ↦ if p i = p j then 1 else 0 := by
  have := Fintype.ofFinite κ
  rw [← AlgEquiv.coe_toAlgHom, map_tensorPowDiagonal, FormallyUnramified.elem_pi R κ, map_sum]
  ext p
  simp [Pi.single_apply, eq_comm]

/-- In the tensor power of the split algebra `κ → R`, viewed as functions on `ι → κ`, the
idempotent `ε` is the indicator of the injective maps. -/
theorem piScalarAlgEquiv_distinctIdempotent [DecidableEq κ] :
    piScalarAlgEquiv R (fun _ : ι ↦ κ) (distinctIdempotent R (κ → R) ι) =
      fun p ↦ if Function.Injective p then 1 else 0 := by
  ext p
  simp only [distinctIdempotent, map_prod, map_sub, map_one, piScalarAlgEquiv_tensorPowDiagonal,
    Finset.prod_apply, Pi.sub_apply, Pi.one_apply]
  split_ifs with hp
  · exact Finset.prod_eq_one fun q hq ↦ by
      simp [hp.ne (Finset.mem_offDiag.mp hq).2.2]
  · obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hp
    exact Finset.prod_eq_zero ((Finset.mem_offDiag (x := (a, b))).mpr
      ⟨Finset.mem_univ a, Finset.mem_univ b, hne⟩) (by simp [hab])

variable (R ι κ) in
/-- The algebra map from the tensor power of `κ → R` to the functions on the embeddings
`ι ↪ κ`, restricting functions on `ι → κ`. -/
private noncomputable def toEmbeddingFun :
    (⨂[R] _ : ι, (κ → R)) →ₐ[R] ((ι ↪ κ) → R) :=
  (AlgHom.pi fun e : ι ↪ κ ↦ Pi.evalAlgHom R (fun _ : ι → κ ↦ R) e).comp
    (piScalarAlgEquiv R fun _ : ι ↦ κ).toAlgHom

omit [DecidableEq ι] in
private theorem toEmbeddingFun_apply (x : ⨂[R] _ : ι, (κ → R)) (e : ι ↪ κ) :
    toEmbeddingFun R ι κ x e = piScalarAlgEquiv R (fun _ : ι ↦ κ) x e := (rfl)

omit [DecidableEq ι] in
private theorem toEmbeddingFun_surjective :
    Function.Surjective (toEmbeddingFun R ι κ) := by
  classical
  intro f
  refine ⟨(piScalarAlgEquiv R fun _ : ι ↦ κ).symm
    fun p ↦ if hp : Function.Injective p then f ⟨p, hp⟩ else 0, funext fun e ↦ ?_⟩
  simp [toEmbeddingFun_apply, e.injective]

private theorem ker_toEmbeddingFun :
    RingHom.ker (toEmbeddingFun R ι κ) =
      Ideal.span {1 - distinctIdempotent R (κ → R) ι} := by
  classical
  refine le_antisymm (fun x hx ↦ Ideal.mem_span_singleton'.mpr ⟨x, ?_⟩) ?_
  · -- `x` vanishes on the injective maps, where `ε` is supported.
    refine (piScalarAlgEquiv R fun _ : ι ↦ κ).injective (funext fun p ↦ ?_)
    rw [map_mul, map_sub, map_one, piScalarAlgEquiv_distinctIdempotent]
    by_cases hp : Function.Injective p
    · have := congrFun (RingHom.mem_ker.mp hx) ⟨p, hp⟩
      rw [toEmbeddingFun_apply, Function.Embedding.coeFn_mk, Pi.zero_apply] at this
      simp [hp, this]
    · simp [hp]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    ext e
    rw [map_sub, map_one, Pi.sub_apply, toEmbeddingFun_apply, piScalarAlgEquiv_distinctIdempotent]
    simp [e.injective]

variable (R ι κ) in
/-- The frame algebra of the split algebra `κ → R` is the algebra of functions on the embeddings
`ι ↪ κ`: an `ι`-tuple of pairwise distinct points of `κ` is an embedding. -/
noncomputable def FrameAlgebra.piEquiv : FrameAlgebra R (κ → R) ι ≃ₐ[R] ((ι ↪ κ) → R) :=
  (Ideal.quotientEquivAlgOfEq R ker_toEmbeddingFun).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective toEmbeddingFun_surjective)

/-- `TauCeti.Algebra.FrameAlgebra.piEquiv` evaluates the class of `x` at an embedding `e` by
evaluating `x`, as a function on `ι → κ`, at `e`. -/
@[simp]
theorem FrameAlgebra.piEquiv_mk (x : ⨂[R] _ : ι, (κ → R)) (e : ι ↪ κ) :
    FrameAlgebra.piEquiv R ι κ (Ideal.Quotient.mk _ x) e =
      piScalarAlgEquiv R (fun _ : ι ↦ κ) x e := (rfl)

/-- Under `TauCeti.Algebra.FrameAlgebra.piEquiv`, a permutation `σ` of the slots acts on
functions on the embeddings `ι ↪ κ` by precomposition with `σ`. -/
theorem FrameAlgebra.piEquiv_smul (σ : Equiv.Perm ι) (y : FrameAlgebra R (κ → R) ι)
    (e : ι ↪ κ) :
    FrameAlgebra.piEquiv R ι κ (σ • y) e =
      FrameAlgebra.piEquiv R ι κ y (σ.toEmbedding.trans e) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [smul_mk, piEquiv_mk, piEquiv_mk, piScalarAlgEquiv_permAlgEquiv, Function.Embedding.coe_trans,
    Equiv.coe_toEmbedding]

variable (R ι) in
/-- The frame algebra of the split algebra `ι → R` indexed by `ι` itself is the algebra of
functions on the permutations of `ι`: the trivial `Perm ι`-torsor. -/
noncomputable def FrameAlgebra.permEquiv :
    FrameAlgebra R (ι → R) ι ≃ₐ[R] (Equiv.Perm ι → R) :=
  (FrameAlgebra.piEquiv R ι ι).trans
    (AlgEquiv.piCongrLeft' R (fun _ ↦ R) (Equiv.embeddingEquivOfFinite ι))

/-- `TauCeti.Algebra.FrameAlgebra.permEquiv` evaluates at a permutation `τ` as
`TauCeti.Algebra.FrameAlgebra.piEquiv` evaluates at the underlying embedding of `τ`. -/
theorem FrameAlgebra.permEquiv_apply (y : FrameAlgebra R (ι → R) ι) (τ : Equiv.Perm ι) :
    FrameAlgebra.permEquiv R ι y τ = FrameAlgebra.piEquiv R ι ι y τ.toEmbedding := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.permEquiv` evaluates the class of `x` at a permutation `τ`
by evaluating `x`, as a function on `ι → ι`, at `τ`. -/
@[simp]
theorem FrameAlgebra.permEquiv_mk (x : ⨂[R] _ : ι, (ι → R)) (τ : Equiv.Perm ι) :
    FrameAlgebra.permEquiv R ι (Ideal.Quotient.mk _ x) τ =
      piScalarAlgEquiv R (fun _ : ι ↦ ι) x τ := by
  rw [permEquiv_apply, piEquiv_mk, Equiv.coe_toEmbedding]

/-- Under `TauCeti.Algebra.FrameAlgebra.permEquiv`, the action of `Perm ι` on the frame algebra
is right translation `(σ • f) τ = f (τ * σ)`: the action on the trivial torsor. -/
theorem FrameAlgebra.permEquiv_smul (σ : Equiv.Perm ι) (y : FrameAlgebra R (ι → R) ι)
    (τ : Equiv.Perm ι) :
    FrameAlgebra.permEquiv R ι (σ • y) τ = FrameAlgebra.permEquiv R ι y (τ * σ) := by
  rw [permEquiv_apply, permEquiv_apply, piEquiv_smul, Equiv.Perm.mul_def, Equiv.trans_toEmbedding]

end Split

end TauCeti.Algebra
