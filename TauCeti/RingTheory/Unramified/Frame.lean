/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.Algebra.TensorProduct.BaseChange
public import TauCeti.RingTheory.Etale.PiTensorProduct
public import TauCeti.RingTheory.PiTensorProduct.Equiv
public import TauCeti.RingTheory.Unramified.Diagonal
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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

is its ring of functions. The permutations of `ι` act on it by permuting the tensor factors, and
the `i`-th slot inclusion `TauCeti.Algebra.FrameAlgebra.slot R S i : S →ₐ[R] FrameAlgebra R S ι`
pulls back functions along the projection to the `i`-th point. Together these assemble into the
*universal frame*

  `TauCeti.Algebra.FrameAlgebra.universalFrame R S ι : P ⊗[R] S →ₐ[P] (ι → P)`,
  `p ⊗ s ↦ (p * slot R S i s)ᵢ`,

where `P = FrameAlgebra R S ι`.

For a split algebra `S = κ → R` the points are the elements of `κ`, and the frame algebra is the
algebra of functions on the embeddings `ι ↪ κ`, with `σ` acting by precomposition with `σ`
(`TauCeti.Algebra.FrameAlgebra.piEquiv`). For `κ = ι` it is the function algebra on `Perm ι`
with right translation, the trivial `Perm ι`-torsor (`TauCeti.Algebra.FrameAlgebra.permEquiv`),
and the universal frame is an isomorphism (`TauCeti.Algebra.FrameAlgebra.universalFrameEquivPi`).

Forming frame algebras and universal frames commutes with base change: for an `R`-algebra `T`, the
frame algebra of `T ⊗[R] S` over `T` is `T ⊗[R] FrameAlgebra R S ι`, compatibly with the
permutation actions (`TauCeti.Algebra.FrameAlgebra.baseChangeEquiv`) and with the universal frame
(`TauCeti.Algebra.FrameAlgebra.universalFrame_baseChange`). Both are also functorial in
isomorphisms of `S` (`TauCeti.Algebra.FrameAlgebra.congr`). Consequently, when `S` becomes
isomorphic to `ι → T` after a faithfully flat base change `R → T`, the universal frame of `S` over
`FrameAlgebra R S ι` is an isomorphism
(`TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi`).

## Main definitions

* `TauCeti.Algebra.tensorPowDiagonal R S i j`: the idempotent `δᵢⱼ` of `⨂[R] _ : ι, S`.
* `TauCeti.Algebra.distinctIdempotent R S ι`: the idempotent `ε = ∏_{i ≠ j} (1 - δᵢⱼ)`.
* `TauCeti.Algebra.FrameAlgebra R S ι`: the frame algebra, with its action of `Equiv.Perm ι`.
* `TauCeti.Algebra.FrameAlgebra.slot R S i`: the `i`-th canonical `R`-algebra map into the frame
  algebra.
* `TauCeti.Algebra.FrameAlgebra.universalFrame R S ι`: the universal frame
  `FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι)`.
* `TauCeti.Algebra.FrameAlgebra.piEquiv`, `TauCeti.Algebra.FrameAlgebra.permEquiv`,
  `TauCeti.Algebra.FrameAlgebra.universalFrameEquivPi`: the frame algebra and universal frame of a
  split algebra.
* `TauCeti.Algebra.FrameAlgebra.baseChangeEquiv`: base change of the frame algebra.
* `TauCeti.Algebra.FrameAlgebra.congr`: the frame algebras of isomorphic algebras are isomorphic.
* `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi`: the universal frame isomorphism
  for an algebra split by a faithfully flat extension.

## Main results

* `TauCeti.Algebra.FrameAlgebra.mk_tensorPowDiagonal`,
  `TauCeti.Algebra.FrameAlgebra.productMap_slot_elem`: distinct slots carry distinct points.
* `TauCeti.Algebra.FrameAlgebra.lift`, `TauCeti.Algebra.FrameAlgebra.liftPi`: the universal
  property of the frame algebra in terms of the tensor power and of families of slot maps.
* `TauCeti.Algebra.FrameAlgebra.smul_mk`, `TauCeti.Algebra.FrameAlgebra.smul_slot`: permutations
  act by permuting tensor factors and slots.
* `TauCeti.Algebra.FrameAlgebra.etale`, `TauCeti.Algebra.FrameAlgebra.finite`: the frame algebra
  of a finite étale algebra is finite étale.
* `TauCeti.Algebra.FrameAlgebra.piEquiv_smul`, `TauCeti.Algebra.FrameAlgebra.permEquiv_smul`:
  equivariance of the split computation.
* `TauCeti.Algebra.map_tensorPowDiagonal_of_span_range_eq_top`,
  `TauCeti.Algebra.map_distinctIdempotent_of_span_range_eq_top`: transport of `δᵢⱼ` and `ε`.
* `TauCeti.Algebra.FrameAlgebra.baseChangeEquiv_map_permAlgEquiv`,
  `TauCeti.Algebra.FrameAlgebra.congr_smul`: equivariance of base change and of `congr`.
* `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_baseChange_iff`,
  `TauCeti.Algebra.FrameAlgebra.bijective_universalFrame_of_algEquiv_pi`: faithfully flat descent
  of bijectivity of the universal frame.

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
  rw [tensorPowDiagonal, ← AlgHom.comp_apply, Algebra.TensorProduct.comp_productMap]

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

/-- The defining equation of `ε` as the product of the complements `1 - δᵢⱼ` over the ordered
pairs of distinct slots. -/
theorem distinctIdempotent_def :
    distinctIdempotent R S ι =
      ∏ p ∈ (Finset.univ : Finset ι).offDiag, (1 - tensorPowDiagonal R S p.1 p.2) := by
  rw [distinctIdempotent]

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

section Slot

variable (R S) in
/-- The `i`-th canonical `R`-algebra map `S → FrameAlgebra R S ι`, placing an element of `S` in
slot `i` of the tensor power and passing to the quotient. Geometrically, this pulls back functions
on `Spec S` along the projection from the scheme of frames to its `i`-th point. -/
noncomputable def slot (i : ι) : S →ₐ[R] FrameAlgebra R S ι :=
  (Ideal.Quotient.mkₐ R _).comp (singleAlgHom (R := R) (A := fun _ : ι ↦ S) i)

/-- `TauCeti.Algebra.FrameAlgebra.slot R S i` sends `s` to the class of `s` placed in slot `i`. -/
theorem slot_apply (i : ι) (s : S) :
    slot R S (ι := ι) i s =
      Ideal.Quotient.mk (Ideal.span {1 - distinctIdempotent R S ι})
        (singleAlgHom (R := R) (A := fun _ : ι ↦ S) i s) := (rfl)

/-- The class of a pure tensor `⨂ₜ xᵢ` in the frame algebra is the product of the slot images
`slot R S i (x i)`. -/
theorem mk_tprod (x : ι → S) :
    Ideal.Quotient.mk (Ideal.span {1 - distinctIdempotent R S ι}) (tprod R x) =
      ∏ i, slot R S i (x i) := by
  rw [tprod_eq_prod_singleAlgHom, map_prod]
  rfl

/-- Two `R`-algebra maps out of the frame algebra agree if and only if they agree on every slot
inclusion `TauCeti.Algebra.FrameAlgebra.slot`. -/
theorem algHom_ext {T : Type*} [Semiring T] [Algebra R T]
    {ψ₁ ψ₂ : FrameAlgebra R S ι →ₐ[R] T}
    (h : ∀ i : ι, ψ₁.comp (slot R S i) = ψ₂.comp (slot R S i)) : ψ₁ = ψ₂ :=
  Ideal.Quotient.algHom_ext R <| PiTensorProduct.algHom_ext fun i ↦ by
    simpa only [slot, AlgHom.comp_assoc] using h i

/-- Distinct slot inclusions into the frame algebra annihilate the diagonal idempotent of `S`. -/
@[simp]
theorem productMap_slot_elem {i j : ι} (hij : i ≠ j) :
    Algebra.TensorProduct.productMap (slot R S (ι := ι) i) (slot R S j)
        (Algebra.FormallyUnramified.elem R S) = 0 := by
  rw [slot, slot, ← map_tensorPowDiagonal, Ideal.Quotient.mkₐ_eq_mk, mk_tensorPowDiagonal hij]

/-- Applying the same slot inclusion to both factors sends the diagonal idempotent to `1`. -/
@[simp]
theorem productMap_slot_self_elem (i : ι) :
    Algebra.TensorProduct.productMap (slot R S (ι := ι) i) (slot R S i)
        (Algebra.FormallyUnramified.elem R S) = 1 := by
  rw [slot, ← map_tensorPowDiagonal, tensorPowDiagonal_self, map_one]

section LiftPi

variable {T : Type*} [CommSemiring T] [Algebra R T]

/-- The universal property of the frame algebra in terms of slot maps: an `ι`-indexed family of
`R`-algebra maps `f i : S →ₐ[R] T` into a commutative `R`-algebra which separates distinct indices,
in the sense that `(f i ⊗ f j)(elem R S) = 0` for `i ≠ j`, induces a unique `R`-algebra map
`FrameAlgebra R S ι →ₐ[R] T` restricting to `f i` on slot `i`. -/
noncomputable def liftPi (f : ι → S →ₐ[R] T)
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0) :
    FrameAlgebra R S ι →ₐ[R] T :=
  lift (PiTensorProduct.productMap f) fun i j hij ↦ by
    rw [map_tensorPowDiagonal, PiTensorProduct.productMap_comp_singleAlgHom,
      PiTensorProduct.productMap_comp_singleAlgHom, hf i j hij]

/-- `TauCeti.Algebra.FrameAlgebra.liftPi f hf` evaluates on slot `i` as `f i`. -/
@[simp]
theorem liftPi_slot (f : ι → S →ₐ[R] T)
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0)
    (i : ι) (s : S) :
    liftPi f hf (slot R S i s) = f i s := by
  rw [slot_apply, liftPi, lift_mk, PiTensorProduct.productMap_singleAlgHom]

/-- `TauCeti.Algebra.FrameAlgebra.liftPi f hf` restricts to `f i` along `slot R S i`. -/
@[simp]
theorem liftPi_comp_slot (f : ι → S →ₐ[R] T)
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0)
    (i : ι) :
    (liftPi f hf).comp (slot R S i) = f i :=
  AlgHom.ext (liftPi_slot f hf i)

/-- `TauCeti.Algebra.FrameAlgebra.liftPi f hf` is the unique `R`-algebra map out of the frame
algebra restricting to `f i` along `slot R S i` for every `i`. -/
theorem eq_liftPi_iff (f : ι → S →ₐ[R] T)
    (hf : ∀ i j, i ≠ j →
      Algebra.TensorProduct.productMap (f i) (f j) (Algebra.FormallyUnramified.elem R S) = 0)
    (ψ : FrameAlgebra R S ι →ₐ[R] T) :
    ψ = liftPi f hf ↔ ∀ i, ψ.comp (slot R S i) = f i :=
  ⟨fun h i ↦ h ▸ liftPi_comp_slot f hf i,
    fun h ↦ algHom_ext fun i ↦ (h i).trans (liftPi_comp_slot f hf i).symm⟩

/-- Every `R`-algebra map out of the frame algebra into a commutative `R`-algebra is
`TauCeti.Algebra.FrameAlgebra.liftPi` of its slot restrictions. -/
@[simp]
theorem liftPi_comp_slot_self (ψ : FrameAlgebra R S ι →ₐ[R] T) :
    liftPi (fun i ↦ ψ.comp (slot R S i)) (fun i j hij ↦ by
      rw [← Algebra.TensorProduct.comp_productMap, AlgHom.comp_apply, productMap_slot_elem hij,
        map_zero]) = ψ :=
  ((eq_liftPi_iff _ _ ψ).mpr fun _ ↦ rfl).symm

end LiftPi

end Slot

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

/-- A permutation `σ` moves `slot R S i s` to `slot R S (σ i) s`. -/
@[simp]
theorem permAlgEquiv_slot (σ : Equiv.Perm ι) (i : ι) (s : S) :
    permAlgEquiv R S ι σ (slot R S i s) = slot R S (σ i) s := by
  rw [slot_apply, ← smul_def, smul_mk, permAlgEquiv_singleAlgHom, ← slot_apply]

/-- A permutation `σ` acts on `slot R S i s` by moving it to slot `σ i`. -/
@[simp]
theorem smul_slot (σ : Equiv.Perm ι) (i : ι) (s : S) :
    σ • slot R S (ι := ι) i s = slot R S (σ i) s :=
  permAlgEquiv_slot σ i s

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

section Transport

variable {R S}
variable {T S' : Type*} [CommRing T] [Algebra R T] [CommRing S'] [Algebra T S'] [Algebra R S']
  [IsScalarTower R T S'] [Algebra.EssFiniteType T S'] [Algebra.FormallyUnramified T S']

section Diagonal

variable {ι : Type*} [DecidableEq ι]

/-- An algebra map `φ` between tensor powers acting on every factor through an algebra map
`f : S → S'` whose image spans `S'` over `T`, such as base change or a surjection, carries the
idempotent `δᵢⱼ` to `δᵢⱼ`. -/
theorem map_tensorPowDiagonal_of_span_range_eq_top (f : S →ₐ[R] S')
    (hf : Submodule.span T (Set.range f) = ⊤) (φ : (⨂[R] _ : ι, S) →ₐ[R] ⨂[T] _ : ι, S')
    (hφ : ∀ k, φ.comp (singleAlgHom k) = ((singleAlgHom k).restrictScalars R).comp f) (i j : ι) :
    φ (tensorPowDiagonal R S i j) = tensorPowDiagonal T S' i j := by
  -- Both sides are images of the diagonal idempotent of `S` under maps agreeing on `a ⊗ b`.
  have h : Algebra.TensorProduct.productMap (((singleAlgHom i).restrictScalars R).comp f)
      (((singleAlgHom j).restrictScalars R).comp f) =
      ((Algebra.TensorProduct.productMap (singleAlgHom (R := T) (A := fun _ : ι ↦ S') i)
        (singleAlgHom j)).restrictScalars R).comp
        (Algebra.TensorProduct.productMap
          ((Algebra.TensorProduct.includeLeft (R := T) (S := R) (B := S')).comp f)
          (((Algebra.TensorProduct.includeRight (R := T) (A := S')).restrictScalars R).comp f)) :=
    Algebra.TensorProduct.ext' fun a b ↦ by simp
  rw [map_tensorPowDiagonal, hφ, hφ, tensorPowDiagonal, ← FormallyUnramified.productMap_elem f hf]
  exact DFunLike.congr_fun h _

/-- An algebra map `φ` between tensor powers acting on every factor through an algebra map
`f : S → S'` whose image spans `S'` over `T` carries the idempotent `ε` of tuples of distinct
points to `ε`. -/
theorem map_distinctIdempotent_of_span_range_eq_top [Fintype ι] (f : S →ₐ[R] S')
    (hf : Submodule.span T (Set.range f) = ⊤) (φ : (⨂[R] _ : ι, S) →ₐ[R] ⨂[T] _ : ι, S')
    (hφ : ∀ k, φ.comp (singleAlgHom k) = ((singleAlgHom k).restrictScalars R).comp f) :
    φ (distinctIdempotent R S ι) = distinctIdempotent T S' ι := by
  simp only [distinctIdempotent_def, map_prod, map_sub, map_one,
    map_tensorPowDiagonal_of_span_range_eq_top f hf φ hφ]

end Diagonal

section BaseChange

variable (T) (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- Base change carries the idempotent `ε` of tuples of distinct points of `S` to that of
`T ⊗[R] S`. -/
theorem baseChangeAlgEquiv_one_tmul_distinctIdempotent :
    PiTensorProduct.baseChangeAlgEquiv T (fun _ : ι ↦ S) (1 ⊗ₜ distinctIdempotent R S ι) =
      distinctIdempotent T (T ⊗[R] S) ι := by
  -- `T ⊗[R] S` is spanned over `T` by the `1 ⊗ s`.
  have hspan : Submodule.span T (Set.range
      (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S)) = ⊤ := by
    have h := Submodule.baseChange_span (R := R) T (Set.univ : Set S)
    rw [Submodule.span_univ, Submodule.baseChange_top, Set.image_univ] at h
    exact h.symm
  exact map_distinctIdempotent_of_span_range_eq_top _ hspan
    (((PiTensorProduct.baseChangeAlgEquiv (R := R) T fun _ : ι ↦ S).toAlgHom.restrictScalars
      R).comp Algebra.TensorProduct.includeRight)
    fun k ↦ AlgHom.ext fun a ↦ by simp [-PiTensorProduct.singleAlgHom_apply]

variable (R S) in
/-- Base change of the frame algebra: the frame algebra of `T ⊗[R] S` over `T` is the base change
of the frame algebra of `S` over `R`. -/
noncomputable def FrameAlgebra.baseChangeEquiv :
    T ⊗[R] FrameAlgebra R S ι ≃ₐ[T] FrameAlgebra T (T ⊗[R] S) ι :=
  (Algebra.TensorProduct.tensorQuotientEquiv T (⨂[R] _ : ι, S) T _).trans <|
    Ideal.quotientEquivAlg _ _ (PiTensorProduct.baseChangeAlgEquiv T fun _ ↦ S) <| by
      rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_sub,
        map_one, Algebra.TensorProduct.includeRight_apply, RingHom.coe_coe, map_sub, map_one,
        baseChangeAlgEquiv_one_tmul_distinctIdempotent]

variable {T ι}

/-- `TauCeti.Algebra.FrameAlgebra.baseChangeEquiv` sends `t ⊗ [x]` to the class of the base change
of `t ⊗ x`. -/
@[simp]
theorem FrameAlgebra.baseChangeEquiv_tmul_mk (t : T) (x : ⨂[R] _ : ι, S) :
    FrameAlgebra.baseChangeEquiv R S T ι (t ⊗ₜ Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (PiTensorProduct.baseChangeAlgEquiv T (fun _ ↦ S) (t ⊗ₜ x)) := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.baseChangeEquiv` is equivariant for the permutations of the
slots, acting on `T ⊗[R] FrameAlgebra R S ι` through the right factor. -/
theorem FrameAlgebra.baseChangeEquiv_map_permAlgEquiv (σ : Equiv.Perm ι)
    (y : T ⊗[R] FrameAlgebra R S ι) :
    FrameAlgebra.baseChangeEquiv R S T ι
        (Algebra.TensorProduct.map (AlgHom.id T T) (permAlgEquiv R S ι σ).toAlgHom y) =
      σ • FrameAlgebra.baseChangeEquiv R S T ι y := by
  induction y using TensorProduct.inductionOn with
  | tmul t z =>
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.coe_toAlgHom, ← smul_def,
      smul_mk, baseChangeEquiv_tmul_mk, baseChangeEquiv_tmul_mk, smul_mk,
      ← PiTensorProduct.baseChangeAlgEquiv_map_permAlgEquiv, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgEquiv.coe_toAlgHom]
  | add y z hy hz => simp only [map_add, hy, hz, smul_def]

/-- `TauCeti.Algebra.FrameAlgebra.baseChangeEquiv` sends `t ⊗ slot R S i s` to
`slot T (T ⊗[R] S) i (t ⊗ s)`. -/
@[simp]
theorem FrameAlgebra.baseChangeEquiv_tmul_slot (t : T) (i : ι) (s : S) :
    FrameAlgebra.baseChangeEquiv R S T ι (t ⊗ₜ slot R S i s) =
      slot T (T ⊗[R] S) i (t ⊗ₜ s) := by
  have h1 : t ⊗ₜ[R] slot R S (ι := ι) i s = t • ((1 : T) ⊗ₜ[R] slot R S i s) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : t ⊗ₜ[R] s = t • ((1 : T) ⊗ₜ[R] s) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, slot_apply, baseChangeEquiv_tmul_mk, baseChangeAlgEquiv_one_tmul_singleAlgHom,
    ← slot_apply, ← map_smul, ← h2]

end BaseChange

end Transport

section Congr

variable {R S}
variable {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra.EssFiniteType R S']
  [Algebra.FormallyUnramified R S'] (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- An isomorphism `S ≃ₐ[R] S'` induces an isomorphism of frame algebras, applying it to every
slot. -/
noncomputable def FrameAlgebra.congr (e : S ≃ₐ[R] S') :
    FrameAlgebra R S ι ≃ₐ[R] FrameAlgebra R S' ι :=
  Ideal.quotientEquivAlg _ _ (PiTensorProduct.congrAlgEquiv fun _ ↦ e) <| by
    have hspan : Submodule.span R (Set.range e.toAlgHom) = ⊤ := by
      rw [AlgEquiv.coe_toAlgHom, e.surjective.range_eq, Submodule.span_univ]
    rw [Ideal.map_span, Set.image_singleton, RingHom.coe_coe, map_sub, map_one,
      ← AlgEquiv.coe_toAlgHom, map_distinctIdempotent_of_span_range_eq_top _ hspan _
        fun k ↦ AlgHom.ext fun a ↦ by simp]

variable {ι}

/-- `TauCeti.Algebra.FrameAlgebra.congr e` sends the class of `x` to the class of `x` with `e`
applied to every slot. -/
@[simp]
theorem FrameAlgebra.congr_mk (e : S ≃ₐ[R] S') (x : ⨂[R] _ : ι, S) :
    FrameAlgebra.congr ι e (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (PiTensorProduct.congrAlgEquiv (fun _ ↦ e) x) := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.congr e` sends `slot R S i s` to `slot R S' i (e s)`. -/
@[simp]
theorem FrameAlgebra.congr_slot (e : S ≃ₐ[R] S') (i : ι) (s : S) :
    FrameAlgebra.congr ι e (slot R S i s) = slot R S' i (e s) := by
  rw [slot_apply, congr_mk, congrAlgEquiv_singleAlgHom, ← slot_apply]

/-- `TauCeti.Algebra.FrameAlgebra.congr e` is equivariant for the permutations of the slots. -/
theorem FrameAlgebra.congr_smul (e : S ≃ₐ[R] S') (σ : Equiv.Perm ι) (y : FrameAlgebra R S ι) :
    FrameAlgebra.congr ι e (σ • y) = σ • FrameAlgebra.congr ι e y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [smul_mk, congr_mk, congr_mk, smul_mk, PiTensorProduct.congrAlgEquiv_permAlgEquiv]

end Congr

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

/-- `TauCeti.Algebra.FrameAlgebra.piEquiv` evaluates `slot R (κ → R) i f` at an embedding `e` as
`f (e i)`. -/
@[simp]
theorem FrameAlgebra.piEquiv_slot (i : ι) (f : κ → R) (e : ι ↪ κ) :
    FrameAlgebra.piEquiv R ι κ (slot R (κ → R) i f) e = f (e i) := by
  rw [slot_apply, piEquiv_mk, piScalarAlgEquiv_singleAlgHom]

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

/-- `TauCeti.Algebra.FrameAlgebra.permEquiv` evaluates `slot R (ι → R) i f` at a permutation `τ` as
`f (τ i)`. -/
@[simp]
theorem FrameAlgebra.permEquiv_slot (i : ι) (f : ι → R) (τ : Equiv.Perm ι) :
    FrameAlgebra.permEquiv R ι (slot R (ι → R) i f) τ = f (τ i) := by
  rw [permEquiv_apply, piEquiv_slot, Equiv.coe_toEmbedding]

/-- Under `TauCeti.Algebra.FrameAlgebra.permEquiv`, the action of `Perm ι` on the frame algebra
is right translation `(σ • f) τ = f (τ * σ)`: the action on the trivial torsor. -/
theorem FrameAlgebra.permEquiv_smul (σ : Equiv.Perm ι) (y : FrameAlgebra R (ι → R) ι)
    (τ : Equiv.Perm ι) :
    FrameAlgebra.permEquiv R ι (σ • y) τ = FrameAlgebra.permEquiv R ι y (τ * σ) := by
  rw [permEquiv_apply, permEquiv_apply, piEquiv_smul, Equiv.Perm.mul_def, Equiv.trans_toEmbedding]

end Split

section UniversalFrame

namespace FrameAlgebra

/-- The *universal frame* of `S` over `FrameAlgebra R S ι`: the `FrameAlgebra R S ι`-algebra
homomorphism `FrameAlgebra R S ι ⊗[R] S → (ι → FrameAlgebra R S ι)` sending `p ⊗ s` to
`i ↦ p * slot R S i s`. Geometrically, base-changing `Spec S → Spec R` to the scheme of frames
exhibits `|ι|` canonical pairwise distinct sections, given by the slot projections. -/
noncomputable def universalFrame :
    FrameAlgebra R S ι ⊗[R] S →ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId (FrameAlgebra R S ι) (ι → FrameAlgebra R S ι))
    (AlgHom.pi (slot R S))

variable {R S ι}

/-- `TauCeti.Algebra.FrameAlgebra.universalFrame` sends `p ⊗ s` at slot `i` to
`p * slot R S i s`. -/
@[simp]
theorem universalFrame_tmul (p : FrameAlgebra R S ι) (s : S) (i : ι) :
    universalFrame R S ι (p ⊗ₜ s) i = p * slot R S i s := by
  simp [universalFrame]

/-- Permuting the frame by `σ` acts on the coordinates of the universal frame and permutes the
slots: `σ • universalFrame R S ι x i` is coordinate `σ i` of the universal frame at `(σ ⊗ id) x`. -/
theorem smul_universalFrame (σ : Equiv.Perm ι) (x : FrameAlgebra R S ι ⊗[R] S) (i : ι) :
    σ • universalFrame R S ι x i =
      universalFrame R S ι
        (Algebra.TensorProduct.map (permAlgEquiv R S ι σ).toAlgHom (AlgHom.id R S) x) (σ i) := by
  induction x using TensorProduct.inductionOn with
  | tmul p s => simp [smul_mul', smul_def]
  | add x y hx hy =>
    simp only [smul_def, map_add, Pi.add_apply] at hx hy ⊢
    rw [hx, hy]

section Congr

variable {S' : Type*} [CommRing S'] [Algebra R S'] [Algebra.EssFiniteType R S']
  [Algebra.FormallyUnramified R S']

/-- The universal frame commutes with `TauCeti.Algebra.FrameAlgebra.congr`. -/
theorem universalFrame_congr (e : S ≃ₐ[R] S') (x : FrameAlgebra R S ι ⊗[R] S) (i : ι) :
    universalFrame R S' ι (Algebra.TensorProduct.congr (congr ι e) e x) i =
      congr ι e (universalFrame R S ι x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul p s => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- Bijectivity of the universal frame is invariant under `R`-algebra isomorphisms of `S`. -/
theorem bijective_universalFrame_congr_iff (e : S ≃ₐ[R] S') :
    Function.Bijective (universalFrame R S' ι) ↔ Function.Bijective (universalFrame R S ι) := by
  let c : (ι → FrameAlgebra R S ι) ≃ₐ[R] (ι → FrameAlgebra R S' ι) :=
    AlgEquiv.piCongrRight fun _ ↦ congr ι e
  have hcomp : ⇑(universalFrame R S' ι) ∘ ⇑(Algebra.TensorProduct.congr (congr ι e) e) =
      ⇑c ∘ ⇑(universalFrame R S ι) :=
    funext fun x ↦ funext fun i ↦ universalFrame_congr e x i
  rw [← Function.Bijective.of_comp_iff _ (Algebra.TensorProduct.congr (congr ι e) e).bijective,
    hcomp, Function.Bijective.of_comp_iff' c.bijective]

end Congr

section BaseChange

/-- Forming the universal frame commutes with base change along `R → T`: read through
`Algebra.TensorProduct.baseChangeTensorAlgEquiv`, `TauCeti.Algebra.FrameAlgebra.baseChangeEquiv`,
and `Algebra.TensorProduct.piRight`, the universal frame of `T ⊗[R] S` over `T` is the base change
of the universal frame of `S` over `R`. -/
theorem universalFrame_baseChange (T : Type*) [CommRing T] [Algebra R T]
    (z : T ⊗[R] (FrameAlgebra R S ι ⊗[R] S)) (i : ι) :
    universalFrame T (T ⊗[R] S) ι
        (Algebra.TensorProduct.congr (baseChangeEquiv R S T ι) AlgEquiv.refl
          (Algebra.TensorProduct.baseChangeTensorAlgEquiv R T (FrameAlgebra R S ι) S z)) i =
      baseChangeEquiv R S T ι
        (Algebra.TensorProduct.piRight R T T (fun _ : ι ↦ FrameAlgebra R S ι)
          (Algebra.TensorProduct.map (AlgHom.id T T)
            ((universalFrame R S ι).restrictScalars R) z) i) := by
  let d := (Algebra.TensorProduct.baseChangeTensorAlgEquiv R T (FrameAlgebra R S ι) S).trans
    (Algebra.TensorProduct.congr (baseChangeEquiv R S T ι) AlgEquiv.refl)
  let c := (Algebra.TensorProduct.piRight R T T fun _ : ι ↦ FrameAlgebra R S ι).trans
    (AlgEquiv.piCongrRight fun _ : ι ↦ baseChangeEquiv R S T ι)
  have hhom :
      ((universalFrame T (T ⊗[R] S) ι).restrictScalars T).comp d.toAlgHom =
        c.toAlgHom.comp
          (Algebra.TensorProduct.map (AlgHom.id T T)
            ((universalFrame R S ι).restrictScalars R)) := by
    apply Algebra.TensorProduct.ext
    · ext
    · refine Algebra.TensorProduct.ext' fun p s ↦ ?_
      ext j
      simp [d, c, ← baseChangeEquiv_tmul_slot, ← map_mul]
  exact congr_fun (DFunLike.congr_fun hhom z) i

/-- Bijectivity of the universal frame descends and ascends along a faithfully flat extension of
the base. -/
theorem bijective_universalFrame_baseChange_iff (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] :
    Function.Bijective (universalFrame T (T ⊗[R] S) ι) ↔
      Function.Bijective (universalFrame R S ι) := by
  let γ : FrameAlgebra R S ι ⊗[R] S →ₗ[R] (ι → FrameAlgebra R S ι) :=
    ((universalFrame R S ι).restrictScalars R).toLinearMap
  let d := (Algebra.TensorProduct.baseChangeTensorAlgEquiv R T (FrameAlgebra R S ι) S).trans
    (Algebra.TensorProduct.congr (baseChangeEquiv R S T ι) AlgEquiv.refl)
  let c := (Algebra.TensorProduct.piRight R T T fun _ : ι ↦ FrameAlgebra R S ι).trans
    (AlgEquiv.piCongrRight fun _ : ι ↦ baseChangeEquiv R S T ι)
  have hmap :
      Algebra.TensorProduct.map (AlgHom.id R T) ((universalFrame R S ι).restrictScalars R) =
        (Algebra.TensorProduct.map (AlgHom.id T T)
          ((universalFrame R S ι).restrictScalars R)).restrictScalars R :=
    Algebra.TensorProduct.ext' fun _ _ ↦ rfl
  have hcomp : ⇑(universalFrame T (T ⊗[R] S) ι) ∘ ⇑d = ⇑c ∘ ⇑(γ.lTensor T) := by
    funext z
    ext i
    simpa only [Function.comp_apply, d, c, AlgEquiv.trans_apply, AlgEquiv.piCongrRight_apply,
      γ, AlgHom.lTensor_toLinearMap_apply, hmap, AlgHom.restrictScalars_apply] using
      universalFrame_baseChange T z i
  rw [← Function.Bijective.of_comp_iff _ d.bijective, hcomp,
    Function.Bijective.of_comp_iff' c.bijective,
    Module.FaithfullyFlat.lTensor_bijective_iff_bijective]
  rfl

end BaseChange

section SplitUniversalFrame

/-- Reindexing coordinate `(i, τ)` to `(τ i, τ)` on `ι → Perm ι → R`: the coordinate change
identifying the universal frame of the split algebra `ι → R` with scalar extension. -/
private def splitUniversalFrameShear (R ι : Type*) [CommSemiring R] :
    (ι → Equiv.Perm ι → R) ≃ₐ[R] (ι → Equiv.Perm ι → R) where
  toFun g i τ := g (τ i) τ
  invFun g k τ := g (τ⁻¹ k) τ
  left_inv g := by ext k τ; simp
  right_inv g := by ext i τ; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable (R ι) in
/-- For the split algebra `ι → R`, the universal frame is bijective: under
`TauCeti.Algebra.FrameAlgebra.permEquiv`, at each permutation `τ : Perm ι` it permutes the `ι`
coordinates by `τ`. -/
theorem bijective_universalFrame_pi :
    Function.Bijective (universalFrame R (ι → R) ι) := by
  let d : FrameAlgebra R (ι → R) ι ⊗[R] (ι → R) ≃ₐ[R] (ι → Equiv.Perm ι → R) :=
    ((Algebra.TensorProduct.congr (permEquiv R ι) AlgEquiv.refl).trans
      (Algebra.TensorProduct.piScalarRight R R (Equiv.Perm ι → R) ι)).trans
      (splitUniversalFrameShear R ι)
  let c : (ι → FrameAlgebra R (ι → R) ι) ≃ₐ[R] (ι → Equiv.Perm ι → R) :=
    AlgEquiv.piCongrRight fun _ ↦ permEquiv R ι
  have hcomp : c.toAlgHom.comp ((universalFrame R (ι → R) ι).restrictScalars R) = d.toAlgHom :=
    Algebra.TensorProduct.ext' fun p f ↦ by
      ext i τ
      simp [c, d, splitUniversalFrameShear, mul_comm]
  have hfn : ⇑c ∘ ⇑(universalFrame R (ι → R) ι) = ⇑d :=
    funext fun x ↦ DFunLike.congr_fun hcomp x
  exact (Function.Bijective.of_comp_iff' c.bijective _).mp (hfn.symm ▸ d.bijective)

variable (R ι) in
/-- The universal frame isomorphism for the split algebra `ι → R`. -/
noncomputable def universalFrameEquivPi :
    FrameAlgebra R (ι → R) ι ⊗[R] (ι → R) ≃ₐ[FrameAlgebra R (ι → R) ι]
      (ι → FrameAlgebra R (ι → R) ι) :=
  AlgEquiv.ofBijective (universalFrame R (ι → R) ι) (bijective_universalFrame_pi R ι)

/-- The underlying function of `TauCeti.Algebra.FrameAlgebra.universalFrameEquivPi` is
`TauCeti.Algebra.FrameAlgebra.universalFrame`. -/
theorem coe_universalFrameEquivPi :
    ⇑(universalFrameEquivPi R ι) = universalFrame R (ι → R) ι := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquivPi` sends `p ⊗ f` at slot `i` to
`p * slot R (ι → R) i f`. -/
@[simp]
theorem universalFrameEquivPi_tmul (p : FrameAlgebra R (ι → R) ι) (f : ι → R) (i : ι) :
    universalFrameEquivPi R ι (p ⊗ₜ f) i = p * slot R (ι → R) i f :=
  universalFrame_tmul p f i

end SplitUniversalFrame

/-- **The universal frame of a locally split algebra is bijective.** If `S` becomes isomorphic to
`ι → T` after a faithfully flat extension `R → T`, then the universal frame of `S` over
`FrameAlgebra R S ι` is bijective. -/
theorem bijective_universalFrame_of_algEquiv_pi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    Function.Bijective (universalFrame R S ι) := by
  rw [← bijective_universalFrame_baseChange_iff T, ← bijective_universalFrame_congr_iff e]
  exact bijective_universalFrame_pi T ι

/-- **The universal frame isomorphism of a locally split algebra.** If `S` becomes isomorphic to
`ι → T` after a faithfully flat extension `R → T`, then base change to `FrameAlgebra R S ι` splits
`S` into `|ι|` copies of `FrameAlgebra R S ι` via the universal frame. -/
noncomputable def universalFrameEquivOfAlgEquivPi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    FrameAlgebra R S ι ⊗[R] S ≃ₐ[FrameAlgebra R S ι] (ι → FrameAlgebra R S ι) :=
  AlgEquiv.ofBijective (universalFrame R S ι) (bijective_universalFrame_of_algEquiv_pi T e)

/-- The underlying function of `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi` is
`TauCeti.Algebra.FrameAlgebra.universalFrame`. -/
theorem coe_universalFrameEquivOfAlgEquivPi (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) :
    ⇑(universalFrameEquivOfAlgEquivPi T e) = universalFrame R S ι := (rfl)

/-- `TauCeti.Algebra.FrameAlgebra.universalFrameEquivOfAlgEquivPi` sends `p ⊗ s` at slot `i` to
`p * slot R S i s`. -/
@[simp]
theorem universalFrameEquivOfAlgEquivPi_tmul (T : Type*) [CommRing T] [Algebra R T]
    [Module.FaithfullyFlat R T] (e : T ⊗[R] S ≃ₐ[T] (ι → T)) (p : FrameAlgebra R S ι) (s : S)
    (i : ι) :
    universalFrameEquivOfAlgEquivPi T e (p ⊗ₜ s) i = p * slot R S i s :=
  universalFrame_tmul p s i

end FrameAlgebra

end UniversalFrame

end TauCeti.Algebra
