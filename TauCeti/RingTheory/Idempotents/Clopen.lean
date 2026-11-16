/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.RingTheory.Idempotents.BaseChange
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum
public import TauCeti.RingTheory.Idempotents.Projective
public import TauCeti.RingTheory.Spectrum.Maximal.Basic
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.Topology.LocallyConstant.Fiber

import Mathlib.Algebra.Module.FinitePresentation

/-!
# Clopen idempotent modules, rank decompositions, and semilocal classification

Let `R` be a commutative ring. Mathlib's `PrimeSpectrum.isIdempotentElemEquivClopens` identifies
idempotents `e : R` with clopen subsets `U` of `Spec R` via `U = D(e)`. For each idempotent `e`,
the principal ideal `Re` is finitely generated projective, linearly isomorphic to the quotient
`R ⧸ (1 - e)`, and has stalk rank `1` on `D(e)` and `0` off it. Orthogonal idempotents add to
products of principal ideals, commutative tensor products multiply idempotents, and balanced
extension of scalars maps `Re` to `S f(e)` for any ring homomorphism `f : R →+* S`.

For a locally constant function `f : PrimeSpectrum R → ℕ`, the compact space `Spec R` forces the
range of `f` to be finite, so the clopen fibers `f⁻¹{k}` yield a complete orthogonal family of
idempotents. Gluing free modules of rank `k` over each fiber defines the finitely generated
projective module `TauCeti.ClopenRankModule R f` of stalk rank `f`, compatible with arbitrary
scalar extension and specializing to `0` and `Rⁿ` on zero and constant functions.

Conversely, any finitely presented flat module `M` decomposes into a finite product of its
constant-rank pieces over the quotients `R ⧸ (1 - e_k)`. Over a nontrivial commutative ring,
`Spec R` is connected if and only if every finitely generated projective module has constant stalk
rank. Over a commutative semilocal ring (`Finite (MaximalSpectrum R)`), every constant-rank
piece is free over its quotient ring by `Module.nonempty_basis_of_flat_of_finrank_eq`, so every
finitely presented flat module is linearly isomorphic to `ClopenRankModule R (rank M)` and is free
whenever `Spec R` is preconnected.

## Main definitions

* `IsIdempotentElem.spanSingletonAddEquivProd`: `R(e + f) ≃ₗ[R] Re × Rf` for orthogonal
  idempotents `e, f` in a semiring.
* `IsIdempotentElem.balancedExtensionSpanSingletonEquiv`: `S ⊗_R Re ≃ₗ[S] S f(e)` along any ring
  homomorphism `f : R →+* S`.
* `IsIdempotentElem.spanSingletonTensorEquiv`: `Re ⊗[R] Rf ≃ₗ[R] R(ef)` in a commutative semiring.
* `IsIdempotentElem.spanSingletonEquivQuotientOneSub`: `Re ≃ₗ[R] R ⧸ (1 - e)` in a commutative
  ring.
* `TauCeti.ClopenRankModule`: the finitely generated projective `R`-module of prescribed locally
  constant rank `f : LocallyConstant (PrimeSpectrum R) ℕ`.
* `Module.rankLocallyConstant` and `Module.ranks`: the stalk rank as a locally constant function
  and its finite set of values.
* `Module.equivPiRankPieces`: the direct-sum decomposition of a finitely presented flat module into
  its constant-rank pieces.

## Main results

* `IsIdempotentElem.rankAtStalk_span_singleton`: `Re` has stalk rank `1` on `D(e)` and `0` off it.
* `PrimeSpectrum.completeOrthogonalIdempotents_isIdempotentElemEquivClopens_symm` and
  `PrimeSpectrum.completeOrthogonalIdempotents_fiberClopens`: a finite clopen partition of `Spec R`
  (in particular the fibers of a locally constant function) gives a complete orthogonal family of
  idempotents.
* `PrimeSpectrum.map_isIdempotentElemEquivClopens_symm`: compatibility of clopen idempotents with
  ring homomorphisms.
* `TauCeti.ClopenRankModule.rankAtStalk_eq`: `ClopenRankModule R f` has stalk rank `f`.
* `TauCeti.connectedSpace_primeSpectrum_iff_forall_finite_projective_rankAtStalk_const`: over a
  nontrivial commutative ring, `Spec R` is connected iff every finite projective has constant rank.
* `TauCeti.nonempty_linearEquiv_clopenRankModule_of_finite_maximalSpectrum`: over a commutative
  semilocal ring, every finitely presented flat module is isomorphic to the clopen-glued module of
  its rank function.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2, pp. 71–72
  and Exercise II.2.6, p. 79.
* The Stacks Project, Tags 00EE and 02M9.
-/

public section

open scoped TensorProduct
open TopologicalSpace

universe u v

/-! ### Principal idempotent ideals -/

namespace IsIdempotentElem

section Semiring

variable {R : Type*} [Semiring R] {e f : R}

/-- For orthogonal idempotents `e` and `f` in a semiring, the principal left ideal `R(e + f)`
splits as the product `Re × Rf`. -/
def spanSingletonAddEquivProd (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) :
    (Ideal.span {e + f} : Ideal R) ≃ₗ[R]
      (Ideal.span {e} : Ideal R) × (Ideal.span {f} : Ideal R) where
  toFun x :=
    (⟨x.1 * e, Ideal.mem_span_singleton'.2 ⟨x.1, rfl⟩⟩,
     ⟨x.1 * f, Ideal.mem_span_singleton'.2 ⟨x.1, rfl⟩⟩)
  map_add' x y := Prod.ext (Subtype.ext (add_mul x.1 y.1 e)) (Subtype.ext (add_mul x.1 y.1 f))
  map_smul' r x := Prod.ext (Subtype.ext (mul_assoc r x.1 e)) (Subtype.ext (mul_assoc r x.1 f))
  invFun p :=
    ⟨p.1.1 + p.2.1, (TauCeti.mem_span_singleton_iff_mul_eq_self
      (he.add hf (by rw [hef, hfe, add_zero]))).2 <| by
        have h1 := (TauCeti.mem_span_singleton_iff_mul_eq_self he).1 p.1.2
        have h2 := (TauCeti.mem_span_singleton_iff_mul_eq_self hf).1 p.2.2
        rw [add_mul, mul_add, mul_add, ← h1, ← h2]
        simp [mul_assoc, he.eq, hf.eq, hef, hfe]⟩
  left_inv x := Subtype.ext <| by
    dsimp only
    rw [← mul_add, (TauCeti.mem_span_singleton_iff_mul_eq_self
      (he.add hf (by rw [hef, hfe, add_zero]))).1 x.2]
  right_inv p := by
    have h1 := (TauCeti.mem_span_singleton_iff_mul_eq_self he).1 p.1.2
    have h2 := (TauCeti.mem_span_singleton_iff_mul_eq_self hf).1 p.2.2
    exact Prod.ext
      (Subtype.ext <| by dsimp only; rw [add_mul, h1, ← h2, mul_assoc, hfe, mul_zero, add_zero])
      (Subtype.ext <| by dsimp only; rw [add_mul, ← h1, mul_assoc, hef, mul_zero, zero_add, h2])

@[simp]
theorem coe_spanSingletonAddEquivProd_fst (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) (x : (Ideal.span {e + f} : Ideal R)) :
    ((he.spanSingletonAddEquivProd hf hef hfe x).1 : R) = x.1 * e := (rfl)

@[simp]
theorem coe_spanSingletonAddEquivProd_snd (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0) (x : (Ideal.span {e + f} : Ideal R)) :
    ((he.spanSingletonAddEquivProd hf hef hfe x).2 : R) = x.1 * f := (rfl)

@[simp]
theorem coe_spanSingletonAddEquivProd_symm (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hef : e * f = 0) (hfe : f * e = 0)
    (p : (Ideal.span {e} : Ideal R) × (Ideal.span {f} : Ideal R)) :
    ((he.spanSingletonAddEquivProd hf hef hfe).symm p : R) = p.1.1 + p.2.1 := (rfl)

end Semiring

section Ring

variable {R S : Type*} [Ring R] [Ring S] (f : R →+* S) {e : R}

/-- Along any ring homomorphism `f : R →+* S`, balanced extension of scalars sends the principal
left ideal `Re` of an idempotent `e` to `S f(e)`. -/
noncomputable def balancedExtensionSpanSingletonEquiv (he : IsIdempotentElem e) :
    TauCeti.BalancedExtension f (Ideal.span {e} : Ideal R) ≃ₗ[S]
      (Ideal.span {f e} : Ideal S) := by
  let g : (Ideal.span {e} : Ideal R) →ₛₗ[f] (Ideal.span {f e} : Ideal S) :=
    { toFun x := ⟨f x.1, (TauCeti.mem_span_singleton_iff_mul_eq_self (he.map f)).2 <| by
        rw [← map_mul, (TauCeti.mem_span_singleton_iff_mul_eq_self he).1 x.2]⟩
      map_add' x y := Subtype.ext (map_add f x.1 y.1)
      map_smul' r x := Subtype.ext (map_mul f r x.1) }
  let inv : (Ideal.span {f e} : Ideal S) →ₗ[S]
      TauCeti.BalancedExtension f (Ideal.span {e} : Ideal R) :=
    (LinearMap.toSpanSingleton S _
      (TauCeti.BalancedExtension.tmul f (1 : S) (TauCeti.spanSingletonGenerator e))).comp
      (Ideal.span {f e} : Ideal S).subtype
  refine LinearEquiv.ofLinearMap (TauCeti.BalancedExtension.lift g) inv
    (LinearMap.ext fun y ↦ Subtype.ext ?_) (TauCeti.BalancedExtension.hom_ext fun x ↦ ?_)
  · simpa [inv, g] using (TauCeti.mem_span_singleton_iff_mul_eq_self (he.map f)).1 y.2
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, TauCeti.BalancedExtension.lift_tmul,
      one_smul, inv, LinearMap.toSpanSingleton_apply, Submodule.subtype_apply, g,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [TauCeti.BalancedExtension.smul_tmul, mul_one, ← one_mul (f x.1),
      ← TauCeti.BalancedExtension.tmul_smul, TauCeti.smul_spanSingletonGenerator he x]

@[simp]
theorem coe_balancedExtensionSpanSingletonEquiv_tmul (he : IsIdempotentElem e)
    (s : S) (x : (Ideal.span {e} : Ideal R)) :
    (he.balancedExtensionSpanSingletonEquiv f (TauCeti.BalancedExtension.tmul f s x) : S) =
      s * f x.1 := by
  simp [balancedExtensionSpanSingletonEquiv]

@[simp]
theorem balancedExtensionSpanSingletonEquiv_symm_apply (he : IsIdempotentElem e)
    (y : (Ideal.span {f e} : Ideal S)) :
    (he.balancedExtensionSpanSingletonEquiv f).symm y =
      y.1 • TauCeti.BalancedExtension.tmul f (1 : S) (TauCeti.spanSingletonGenerator e) := by
  simp [balancedExtensionSpanSingletonEquiv]

end Ring

section CommSemiring

variable {R : Type*} [CommSemiring R] {e f : R}

/-- In a commutative semiring, the tensor product `Re ⊗[R] Rf` of two principal idempotent ideals
is linearly isomorphic to `R(ef)`. -/
noncomputable def spanSingletonTensorEquiv (he : IsIdempotentElem e) (hf : IsIdempotentElem f) :
    (Ideal.span {e} : Ideal R) ⊗[R] (Ideal.span {f} : Ideal R) ≃ₗ[R]
      (Ideal.span {e * f} : Ideal R) := by
  let bil : (Ideal.span {e} : Ideal R) →ₗ[R] (Ideal.span {f} : Ideal R) →ₗ[R]
      (Ideal.span {e * f} : Ideal R) :=
    LinearMap.mk₂ R
      (fun x y ↦ ⟨x.1 * y.1, (TauCeti.mem_span_singleton_iff_mul_eq_self (he.mul hf)).2 <| by
        rw [mul_mul_mul_comm, (TauCeti.mem_span_singleton_iff_mul_eq_self he).1 x.2,
          (TauCeti.mem_span_singleton_iff_mul_eq_self hf).1 y.2]⟩)
      (fun _ _ _ ↦ Subtype.ext (add_mul _ _ _)) (fun _ _ _ ↦ Subtype.ext (mul_assoc _ _ _))
      (fun _ _ _ ↦ Subtype.ext (mul_add _ _ _)) (fun _ _ _ ↦ Subtype.ext (by simp [mul_left_comm]))
  let incl : (Ideal.span {e * f} : Ideal R) →ₗ[R] (Ideal.span {e} : Ideal R) :=
    Submodule.inclusion (Ideal.span_singleton_le_span_singleton.2 ⟨f, rfl⟩)
  let inv : (Ideal.span {e * f} : Ideal R) →ₗ[R]
      (Ideal.span {e} : Ideal R) ⊗[R] (Ideal.span {f} : Ideal R) :=
    (TensorProduct.mk R _ _).flip (TauCeti.spanSingletonGenerator f) ∘ₗ incl
  refine LinearEquiv.ofLinearMap (TensorProduct.lift bil) inv
    (LinearMap.ext fun z ↦ Subtype.ext ?_) (TensorProduct.ext' fun x y ↦ ?_)
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, inv, LinearMap.flip_apply,
      TensorProduct.mk_apply, TensorProduct.lift.tmul, bil, LinearMap.mk₂_apply, incl,
      Submodule.coe_inclusion, TauCeti.coe_spanSingletonGenerator]
    have hz := (TauCeti.mem_span_singleton_iff_mul_eq_self (he.mul hf)).1 z.2
    rw [← hz, mul_assoc, mul_assoc, hf.eq, hz]
  · simp only [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.lift.tmul, inv,
      LinearMap.flip_apply, TensorProduct.mk_apply]
    rw [show incl (bil x y) = y.1 • x from Subtype.ext (by simp [incl, bil, mul_comm]),
      TensorProduct.smul_tmul, TauCeti.smul_spanSingletonGenerator hf y]

@[simp]
theorem coe_spanSingletonTensorEquiv_tmul (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (x : (Ideal.span {e} : Ideal R)) (y : (Ideal.span {f} : Ideal R)) :
    (he.spanSingletonTensorEquiv hf (x ⊗ₜ[R] y) : R) = x.1 * y.1 := by
  simp [spanSingletonTensorEquiv]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {e : R}

/-- In a commutative ring, the principal ideal `Re` of an idempotent `e` is linearly isomorphic to
the quotient `R ⧸ (1 - e)`. -/
def spanSingletonEquivQuotientOneSub (he : IsIdempotentElem e) :
    (Ideal.span {e} : Ideal R) ≃ₗ[R] R ⧸ Ideal.span {1 - e} := by
  let fwd : (Ideal.span {e} : Ideal R) →ₗ[R] R ⧸ Ideal.span {1 - e} :=
    (Ideal.span {1 - e} : Ideal R).mkQ.comp (Ideal.span {e} : Ideal R).subtype
  let inv : (R ⧸ Ideal.span {1 - e}) →ₗ[R] (Ideal.span {e} : Ideal R) :=
    (Ideal.span {1 - e}).liftQ
      (LinearMap.toSpanSingleton R (Ideal.span {e} : Ideal R) (TauCeti.spanSingletonGenerator e))
      (fun r hr ↦ by
        obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
        exact LinearMap.mem_ker.2 <| Subtype.ext <| by
          simp [mul_assoc, sub_mul, he.eq])
  refine LinearEquiv.ofLinearMap fwd inv (LinearMap.ext fun q ↦ ?_) (LinearMap.ext fun x ↦ ?_)
  · refine Submodule.Quotient.induction_on _ q fun r ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, inv, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply, fwd, Submodule.mkQ_apply, Submodule.subtype_apply]
    refine (Submodule.Quotient.eq _).2 ?_
    simpa [TauCeti.coe_spanSingletonGenerator] using
      (Ideal.mem_span_singleton'.2 ⟨-r, by ring⟩ : r * e - r ∈ Ideal.span {1 - e})
  · apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply, fwd, Submodule.mkQ_apply,
      Submodule.subtype_apply, inv, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply,
      SetLike.val_smul, smul_eq_mul, TauCeti.coe_spanSingletonGenerator]
    exact (TauCeti.mem_span_singleton_iff_mul_eq_self he).1 x.2

@[simp]
theorem spanSingletonEquivQuotientOneSub_apply (he : IsIdempotentElem e)
    (x : (Ideal.span {e} : Ideal R)) :
    he.spanSingletonEquivQuotientOneSub x = Ideal.Quotient.mk (Ideal.span {1 - e}) x.1 := by
  simp [spanSingletonEquivQuotientOneSub]

@[simp]
theorem coe_spanSingletonEquivQuotientOneSub_symm_mk (he : IsIdempotentElem e) (r : R) :
    (he.spanSingletonEquivQuotientOneSub.symm (Ideal.Quotient.mk _ r) : R) = r * e :=
  congrArg Subtype.val <|
    (show he.spanSingletonEquivQuotientOneSub.symm (Ideal.Quotient.mk _ r) =
        ⟨r * e, Ideal.mem_span_singleton'.2 ⟨r, rfl⟩⟩ from
      he.spanSingletonEquivQuotientOneSub.symm_apply_eq.2 <| by
        rw [spanSingletonEquivQuotientOneSub_apply, Ideal.Quotient.eq]
        exact Ideal.mem_span_singleton'.2 ⟨r, by ring⟩)

/-- For an idempotent `e` in a commutative ring `R`, the quotient `R ⧸ (1 - e)` is a projective
`R`-module. -/
theorem projective_quotient_span_one_sub (he : IsIdempotentElem e) :
    Module.Projective R (R ⧸ Ideal.span {1 - e}) :=
  have := he.projective_span_singleton
  Module.Projective.of_equiv he.spanSingletonEquivQuotientOneSub

open scoped Classical in
/-- The principal ideal `Re` of an idempotent `e` has stalk rank `1` on `D(e)` and `0` off it. -/
theorem rankAtStalk_span_singleton (he : IsIdempotentElem e) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Ideal.span {e} : Ideal R) p = if e ∈ p.asIdeal then 0 else 1 :=
  (congrFun (Module.rankAtStalk_eq_of_equiv he.spanSingletonEquivQuotientOneSub) p).trans
    (Module.rankAtStalk_quotient_span_one_sub he p)

end CommRing

end IsIdempotentElem

/-! ### Clopen idempotents on `PrimeSpectrum` -/

namespace PrimeSpectrum

section CommRing

variable {R : Type*} [CommRing R]

/-- The idempotent of a clopen `U` lies in a prime ideal `p` if and only if `p ∉ U`. -/
theorem mem_asIdeal_isIdempotentElemEquivClopens_symm_iff
    (U : Clopens (PrimeSpectrum R)) (p : PrimeSpectrum R) :
    (isIdempotentElemEquivClopens.symm U).1 ∈ p.asIdeal ↔ p ∉ U := by
  have h : p ∈ basicOpen (isIdempotentElemEquivClopens.symm U).1 ↔ p ∈ U := by
    rw [basicOpen_isIdempotentElemEquivClopens_symm]; rfl
  exact (not_iff_comm.1 h).symm

/-- Disjoint clopens have orthogonal idempotents. -/
theorem isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint
    {U V : Clopens (PrimeSpectrum R)} (h : Disjoint U V) :
    (isIdempotentElemEquivClopens.symm U).1 * (isIdempotentElemEquivClopens.symm V).1 = 0 := by
  have hinf := congrArg Subtype.val (isIdempotentElemEquivClopens_symm_inf (R := R) U V)
  rw [h.eq_bot, isIdempotentElemEquivClopens_symm_bot] at hinf
  exact hinf.symm

/-- The idempotent of a disjoint union of two clopens is the sum of their idempotents. -/
theorem isIdempotentElemEquivClopens_symm_sup_of_disjoint
    {U V : Clopens (PrimeSpectrum R)} (h : Disjoint U V) :
    (isIdempotentElemEquivClopens.symm (U ⊔ V)).1 =
      (isIdempotentElemEquivClopens.symm U).1 + (isIdempotentElemEquivClopens.symm V).1 := by
  rw [congrArg Subtype.val (isIdempotentElemEquivClopens_symm_sup (R := R) U V)]
  dsimp only
  rw [isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint h, sub_zero]

/-- The idempotent of a finite pairwise-disjoint union of clopens is the sum of their
idempotents. -/
theorem isIdempotentElemEquivClopens_symm_finset_sup {ι : Type*} (s : Finset ι)
    (U : ι → Clopens (PrimeSpectrum R)) (hdisj : (s : Set ι).PairwiseDisjoint U) :
    (isIdempotentElemEquivClopens.symm (s.sup U)).1 =
      ∑ i ∈ s, (isIdempotentElemEquivClopens.symm (U i)).1 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty, Finset.sum_empty, isIdempotentElemEquivClopens_symm_bot]
  | insert a s ha ih =>
    have hda : Disjoint (U a) (s.sup U) := Finset.disjoint_sup_right.2 fun b hb ↦
      hdisj (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hb) (fun h ↦ ha (h ▸ hb))
    rw [Finset.sup_insert, isIdempotentElemEquivClopens_symm_sup_of_disjoint hda,
      Finset.sum_insert ha, ih (hdisj.subset (Finset.subset_insert a s))]

/-- A finite clopen partition of `Spec R` gives a complete orthogonal family of idempotents. -/
theorem completeOrthogonalIdempotents_isIdempotentElemEquivClopens_symm {ι : Type*} [Fintype ι]
    (U : ι → Clopens (PrimeSpectrum R)) (hdisj : Pairwise (Function.onFun Disjoint U))
    (hcover : Finset.univ.sup U = ⊤) :
    CompleteOrthogonalIdempotents fun i ↦ (isIdempotentElemEquivClopens.symm (U i)).1 where
  idem i := (isIdempotentElemEquivClopens.symm (U i)).2
  ortho _ _ hij := isIdempotentElemEquivClopens_symm_mul_eq_zero_of_disjoint (hdisj hij)
  complete := by
    rw [← isIdempotentElemEquivClopens_symm_finset_sup Finset.univ U (fun _ _ _ _ h ↦ hdisj h),
      hcover, isIdempotentElemEquivClopens_symm_top]

/-- A ring homomorphism carries the idempotent of a clopen `U ⊆ Spec R` to the idempotent of its
preimage in `Spec S`. -/
theorem map_isIdempotentElemEquivClopens_symm {S : Type*} [CommRing S] (f : R →+* S)
    (U : Clopens (PrimeSpectrum R)) :
    f (isIdempotentElemEquivClopens.symm U).1 =
      (isIdempotentElemEquivClopens.symm
        ⟨comap f ⁻¹' U, U.isClopen.preimage (continuous_comap f)⟩).1 := by
  apply basicOpen_injOn_isIdempotentElem ((isIdempotentElemEquivClopens.symm U).2.map f)
    (isIdempotentElemEquivClopens.symm _).2
  rw [← comap_basicOpen, basicOpen_isIdempotentElemEquivClopens_symm,
    basicOpen_isIdempotentElemEquivClopens_symm]
  rfl

/-- The idempotents attached to the clopen fibers of a locally constant function on `Spec R` form
a complete orthogonal family indexed by the finite range of the function. -/
theorem completeOrthogonalIdempotents_fiberClopens {α : Type*}
    (f : LocallyConstant (PrimeSpectrum R) α) :
    CompleteOrthogonalIdempotents
      fun a : f.range_finite.toFinset ↦
        (isIdempotentElemEquivClopens.symm (f.fiberClopens a.1)).1 :=
  completeOrthogonalIdempotents_isIdempotentElemEquivClopens_symm _
    (fun _ _ hab ↦ f.pairwise_disjoint_fiberClopens (Subtype.coe_ne_coe.2 hab))
    (by simpa [Finset.sup_coe] using f.finset_sup_fiberClopens)

end CommRing

end PrimeSpectrum

/-! ### Clopen-glued modules and rank-piece decompositions -/

open PrimeSpectrum (isIdempotentElemEquivClopens)

namespace TauCeti

/-- The finitely generated projective `R`-module obtained by gluing free modules of rank `f p`
along the clopen rank fibers of a locally constant function `f : PrimeSpectrum R → ℕ`. -/
def ClopenRankModule (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    Type u :=
  ∀ k : f.range_finite.toFinset, Fin k.1 →
    (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R)

namespace ClopenRankModule

variable (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ)

noncomputable instance instAddCommGroup : AddCommGroup (ClopenRankModule R f) :=
  inferInstanceAs (AddCommGroup (∀ k : f.range_finite.toFinset, Fin k.1 →
    (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R)))

noncomputable instance instModule : Module R (ClopenRankModule R f) :=
  inferInstanceAs (Module R (∀ k : f.range_finite.toFinset, Fin k.1 →
    (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R)))

/-- The defining identification of `ClopenRankModule R f` with the product over the finite range
of `f`. -/
noncomputable def equivPi :
    ClopenRankModule R f ≃ₗ[R]
      ∀ k : f.range_finite.toFinset, Fin k.1 →
        (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R) :=
  LinearEquiv.refl R _

instance instFinite : Module.Finite R (ClopenRankModule R f) :=
  have (k : f.range_finite.toFinset) : Module.Finite R
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R) :=
    Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _)
  Module.Finite.equiv (equivPi R f).symm

instance instProjective : Module.Projective R (ClopenRankModule R f) :=
  have (k : f.range_finite.toFinset) : Module.Projective R
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R) :=
    (isIdempotentElemEquivClopens.symm _).2.projective_span_singleton
  have (k : f.range_finite.toFinset) : Module.Projective R (Fin k.1 →
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R)) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R))
  Module.Projective.of_equiv
    ((DFinsupp.linearEquivFunOnFintype (R := R)).trans (equivPi R f).symm)

/-- `ClopenRankModule R f` has stalk rank `f p` at every prime `p`. -/
@[simp]
theorem rankAtStalk_eq (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (ClopenRankModule R f) p = f p := by
  have (k : f.range_finite.toFinset) : Module.Projective R
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R) :=
    (isIdempotentElemEquivClopens.symm _).2.projective_span_singleton
  have (k : f.range_finite.toFinset) : Module.Finite R
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R) :=
    Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _)
  have (k : f.range_finite.toFinset) : Module.Projective R (Fin k.1 →
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R)) :=
    Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R))
  have (k : f.range_finite.toFinset) : Module.Flat R (Fin k.1 →
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.1)).1} : Ideal R)) :=
    Module.Flat.of_projective
  rw [Module.rankAtStalk_eq_of_equiv (equivPi R f), Module.rankAtStalk_pi,
    finsum_eq_sum_of_fintype,
    Finset.sum_eq_single_of_mem ⟨f p, f.range_finite.mem_toFinset.2 ⟨p, rfl⟩⟩ (Finset.mem_univ _)]
  · rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype]
    simp [(isIdempotentElemEquivClopens.symm _).2.rankAtStalk_span_singleton,
      PrimeSpectrum.mem_asIdeal_isIdempotentElemEquivClopens_symm_iff]
  · intro k _ hkne
    rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype]
    have hne : f p ≠ k.1 := fun h ↦ hkne (Subtype.ext h.symm)
    simp [(isIdempotentElemEquivClopens.symm _).2.rankAtStalk_span_singleton,
      PrimeSpectrum.mem_asIdeal_isIdempotentElemEquivClopens_symm_iff, hne]

/-- The clopen-glued module for the zero rank function is trivial. -/
instance subsingleton_zero : Subsingleton (ClopenRankModule R 0) :=
  let z : LocallyConstant (PrimeSpectrum R) ℕ := 0
  (equivPi R z).toEquiv.subsingleton_congr.2 <|
    have (k : z.range_finite.toFinset) : Subsingleton (Fin k.1 →
        (Ideal.span {(isIdempotentElemEquivClopens.symm (z.fiberClopens k.1)).1} : Ideal R)) := by
      obtain ⟨_, hp⟩ := z.range_finite.mem_toFinset.1 k.2
      rw [show k.1 = 0 from hp.symm]; infer_instance
    inferInstance

/-- The clopen-glued module for the constant rank function `n` is linearly isomorphic to `Rⁿ`. -/
noncomputable def constEquiv (n : ℕ) :
    ClopenRankModule R (LocallyConstant.const (PrimeSpectrum R) n) ≃ₗ[R] (Fin n → R) := by
  classical
  by_cases hR : Subsingleton R
  · have := Module.subsingleton R (ClopenRankModule R (LocallyConstant.const (PrimeSpectrum R) n))
    have := Module.subsingleton R (Fin n → R)
    exact LinearEquiv.ofSubsingleton _ _
  · have : Nontrivial R := not_subsingleton_iff_nontrivial.1 hR
    let c := LocallyConstant.const (PrimeSpectrum R) n
    let k₀ : c.range_finite.toFinset :=
      ⟨n, c.range_finite.mem_toFinset.2 ⟨Classical.arbitrary _, rfl⟩⟩
    have huniq (k : c.range_finite.toFinset) : k = k₀ :=
      let ⟨_, hp⟩ := c.range_finite.mem_toFinset.1 k.2; Subtype.ext hp.symm
    have he1 : (isIdempotentElemEquivClopens.symm (c.fiberClopens n)).1 = 1 := by
      rw [show c.fiberClopens n = ⊤ from Clopens.ext (by ext; simp [c]),
        PrimeSpectrum.isIdempotentElemEquivClopens_symm_top]
    exact (equivPi R c).trans
      { toFun x i := (x k₀ i : R)
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        invFun y k i := ⟨y (Fin.cast (congrArg Subtype.val (huniq k)) i), by
          have hek : (isIdempotentElemEquivClopens.symm (c.fiberClopens k.1)).1 = 1 := by
            rw [show k.1 = n from congrArg Subtype.val (huniq k), he1]
          rw [hek, Ideal.span_singleton_one]; trivial⟩
        left_inv x := by funext k; cases huniq k; rfl
        right_inv _ := rfl }

/-- Restricting the product defining `ClopenRankModule` from a larger finite index set containing
the range of `g` drops only zero factors. -/
private noncomputable def piRestrictRangeEquiv {S : Type v} [CommRing S]
    (g : LocallyConstant (PrimeSpectrum S) ℕ) {s : Finset ℕ}
    (hsub : g.range_finite.toFinset ⊆ s) :
    (∀ k : s, Fin k.1 →
      (Ideal.span {(isIdempotentElemEquivClopens.symm (g.fiberClopens k.1)).1} : Ideal S)) ≃ₗ[S]
    (∀ k : g.range_finite.toFinset, Fin k.1 →
      (Ideal.span {(isIdempotentElemEquivClopens.symm (g.fiberClopens k.1)).1} : Ideal S)) := by
  classical
  refine
    { toFun x k := x ⟨k.1, hsub k.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      invFun y k := if hk : k.1 ∈ g.range_finite.toFinset then y ⟨k.1, hk⟩ else 0
      left_inv x := funext fun k ↦ funext fun j ↦ ?_
      right_inv y := by funext k j; simp [k.2] }
  by_cases hk : k.1 ∈ g.range_finite.toFinset
  · simp [hk]
  · simp only [hk, ↓reduceDIte, Pi.zero_apply]
    have hbot : g.fiberClopens k.1 = ⊥ := Clopens.ext <| Set.eq_empty_iff_forall_notMem.2
      fun q hq ↦ hk (g.range_finite.mem_toFinset.2 ⟨q, by simpa using hq⟩)
    have : Subsingleton
        (Ideal.span {(isIdempotentElemEquivClopens.symm (g.fiberClopens k.1)).1} : Ideal S) := by
      rw [hbot, PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot, Ideal.span_singleton_zero]
      infer_instance
    exact Subsingleton.elim _ _

/-- Extension of scalars along `φ : R →+* S` carries `ClopenRankModule R f` to the clopen-glued
module of the pulled-back rank function on `Spec S`. -/
noncomputable def balancedExtensionEquiv {S : Type v} [CommRing S] (φ : R →+* S) :
    BalancedExtension φ (ClopenRankModule R f) ≃ₗ[S]
      ClopenRankModule S (f.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) := by
  let f' := f.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩
  have hsub : f'.range_finite.toFinset ⊆ f.range_finite.toFinset := fun k hk ↦
    let ⟨q, hq⟩ := f'.range_finite.mem_toFinset.1 hk
    f.range_finite.mem_toFinset.2 ⟨PrimeSpectrum.comap φ q, hq⟩
  have hmap (k : ℕ) : φ (isIdempotentElemEquivClopens.symm (f.fiberClopens k)).1 =
      (isIdempotentElemEquivClopens.symm (f'.fiberClopens k)).1 := by
    rw [PrimeSpectrum.map_isIdempotentElemEquivClopens_symm φ (f.fiberClopens k)]
    congr 2; ext q; simp [f']
  exact ((BalancedExtension.congr φ (equivPi R f)).trans <|
    (BalancedExtension.piEquiv φ _ _).trans <|
      LinearEquiv.piCongrRight fun k ↦
        (BalancedExtension.piEquiv φ _ _).trans <|
          LinearEquiv.piCongrRight fun _ ↦
            ((isIdempotentElemEquivClopens.symm _).2.balancedExtensionSpanSingletonEquiv φ).trans
              (LinearEquiv.ofEq _ _ (by rw [hmap]))).trans
    ((piRestrictRangeEquiv f' hsub).trans (equivPi S f').symm)

end ClopenRankModule

end TauCeti

/-! ### Rank-value sets and constant-rank decompositions -/

namespace Module

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [Module.FinitePresentation R M] [Module.Flat R M]

/-- The stalk rank of a finitely presented flat module, bundled as a locally constant function
on `Spec R`. -/
noncomputable def rankLocallyConstant : LocallyConstant (PrimeSpectrum R) ℕ :=
  ⟨rankAtStalk M, isLocallyConstant_rankAtStalk⟩

@[simp]
theorem rankLocallyConstant_apply (p : PrimeSpectrum R) :
    rankLocallyConstant R M p = rankAtStalk M p := (rfl)

/-- The finite set of stalk-rank values attained by a finitely presented flat module `M`. -/
noncomputable def ranks : Finset ℕ :=
  (rankLocallyConstant R M).range_finite.toFinset

@[simp]
theorem mem_ranks_iff {k : ℕ} : k ∈ ranks R M ↔ ∃ p : PrimeSpectrum R, rankAtStalk M p = k := by
  simp [ranks]

/-- Over a nontrivial commutative ring, `Rⁿ` has rank-value set `{n}`. -/
theorem ranks_fin_fun [Nontrivial R] (n : ℕ) : ranks R (Fin n → R) = {n} := by
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  ext k; simp only [mem_ranks_iff, Finset.mem_singleton, rankAtStalk_fin_fun]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨p₀, h.symm⟩⟩

/-- Over a nontrivial commutative ring, a subsingleton module has rank-value set `{0}`. -/
theorem ranks_subsingleton [Nontrivial R] [Subsingleton M] : ranks R M = {0} := by
  obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  ext k; simp only [mem_ranks_iff, Finset.mem_singleton, rankAtStalk_eq_zero_of_subsingleton,
    Pi.zero_apply]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨p₀, h.symm⟩⟩

/-- Over the zero ring, every module has empty rank-value set. -/
theorem ranks_eq_empty_of_subsingleton [Subsingleton R] : ranks R M = ∅ := by
  ext k; simp only [mem_ranks_iff, Finset.notMem_empty, iff_false, not_exists]
  exact fun p ↦ (not_nontrivial R (PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨p⟩)).elim

/-- The idempotents attached to the constant-rank loci of a finitely presented flat module form a
complete orthogonal family. -/
theorem completeOrthogonalIdempotents_rank :
    CompleteOrthogonalIdempotents fun k : ranks R M ↦
      (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.1)).1 :=
  PrimeSpectrum.completeOrthogonalIdempotents_fiberClopens (rankLocallyConstant R M)

/-- A finitely presented flat module splits as the product of its base changes to the quotients
cutting out its constant-rank loci. -/
noncomputable def equivPiRankPieces :
    M ≃ₗ[R] ∀ k : ranks R M,
      (R ⧸ Ideal.span
        {1 - (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.1)).1})
        ⊗[R] M :=
  (completeOrthogonalIdempotents_rank R M).moduleTensorProductEquiv M

/-- Over the quotient ring cutting out the rank-`k` locus, the corresponding piece of `M` has
constant stalk rank `k`. -/
theorem rankAtStalk_rankPiece (k : ranks R M)
    (q : PrimeSpectrum (R ⧸ Ideal.span
      {1 - (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.1)).1})) :
    rankAtStalk ((R ⧸ Ideal.span
      {1 - (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.1)).1})
      ⊗[R] M) q = k.1 := by
  let e := (isIdempotentElemEquivClopens.symm ((rankLocallyConstant R M).fiberClopens k.1)).1
  have he : IsIdempotentElem e := (isIdempotentElemEquivClopens.symm _).2
  rw [rankAtStalk_baseChange]
  have hD : q.comap (algebraMap R (R ⧸ Ideal.span {1 - e})) ∈ PrimeSpectrum.basicOpen e := by
    rw [← SetLike.mem_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he,
      PrimeSpectrum.mem_zeroLocus]
    rintro x (rfl : x = 1 - e); simp [PrimeSpectrum.comap]
  rw [PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm] at hD
  exact LocallyConstant.mem_fiberClopens.1 hD

end Module

/-! ### Connectedness criterion and semilocal classification -/

namespace TauCeti

/-- **Connectedness of `Spec R` via constant rank.** Over a nontrivial commutative ring `R`, the
prime spectrum is connected if and only if every finitely generated projective `R`-module has
constant stalk rank. -/
theorem connectedSpace_primeSpectrum_iff_forall_finite_projective_rankAtStalk_const
    (R : Type u) [CommRing R] [Nontrivial R] :
    ConnectedSpace (PrimeSpectrum R) ↔
      ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P],
        ∃ n : ℕ, ∀ p : PrimeSpectrum R, Module.rankAtStalk (R := R) P p = n := by
  refine ⟨fun hconn P _ _ _ _ ↦ ?_, fun hconst ↦ ?_⟩
  · have := Module.finitePresentation_of_projective R P
    obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    exact ⟨Module.rankAtStalk P p₀, fun p ↦
      (Module.isLocallyConstant_rankAtStalk (R := R) (M := P)).apply_eq_of_preconnectedSpace p p₀⟩
  · refine connectedSpace_primeSpectrum_iff_idempotent_eq_zero_or_one.2 fun e he ↦ ?_
    have : Module.Finite R (Ideal.span {e} : Ideal R) :=
      Module.Finite.iff_fg.2 (Submodule.fg_span_singleton e)
    have : Module.Projective R (Ideal.span {e} : Ideal R) := he.projective_span_singleton
    obtain ⟨n, hn⟩ := hconst (Ideal.span {e} : Ideal R)
    obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    classical
    have hconst' (p : PrimeSpectrum R) :
        (if e ∈ p.asIdeal then 0 else 1) = (if e ∈ p₀.asIdeal then 0 else 1) := by
      rw [← he.rankAtStalk_span_singleton, ← he.rankAtStalk_span_singleton, hn p, hn p₀]
    by_cases hmem : e ∈ p₀.asIdeal
    · left; refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .zero ?_
      ext p; simpa [hmem] using hconst' p
    · right; refine PrimeSpectrum.basicOpen_injOn_isIdempotentElem he .one ?_
      ext p; simpa [hmem] using hconst' p

/-- **Semilocal module classification.** Over a commutative semilocal ring, every finitely
presented flat module `M` is linearly isomorphic to `ClopenRankModule R (rank M)`. -/
theorem nonempty_linearEquiv_clopenRankModule_of_finite_maximalSpectrum
    {R : Type u} [CommRing R] [Finite (MaximalSpectrum R)]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    Nonempty (M ≃ₗ[R] ClopenRankModule R (Module.rankLocallyConstant R M)) := by
  let r := Module.rankLocallyConstant R M
  have hpiece (k : Module.ranks R M) : Nonempty
      (((R ⧸ Ideal.span {1 - (isIdempotentElemEquivClopens.symm (r.fiberClopens k.1)).1}) ⊗[R] M)
        ≃ₗ[R] (Fin k.1 →
          (Ideal.span
            {(isIdempotentElemEquivClopens.symm (r.fiberClopens k.1)).1} : Ideal R))) := by
    let e := (isIdempotentElemEquivClopens.symm (r.fiberClopens k.1)).1
    let Rk := R ⧸ Ideal.span {1 - e}
    obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq Rk (Rk ⊗[R] M) k.1 fun P ↦ by
      rw [Module.finrank_quotient_tensorProduct_eq_rankAtStalk]
      exact Module.rankAtStalk_rankPiece R M k P.toPrimeSpectrum
    exact ⟨(b.equivFun.restrictScalars R).trans <| LinearEquiv.piCongrRight fun _ ↦
      (isIdempotentElemEquivClopens.symm _).2.spanSingletonEquivQuotientOneSub.symm⟩
  exact ⟨(Module.equivPiRankPieces R M).trans
    ((LinearEquiv.piCongrRight fun k ↦ Classical.choice (hpiece k)).trans
      (ClopenRankModule.equivPi R r).symm)⟩

/-- Over a commutative semilocal ring with preconnected prime spectrum (for instance a local ring
or a connected semilocal domain), every finitely presented flat module is free. -/
theorem free_of_finite_maximalSpectrum_of_preconnectedSpace
    {R : Type u} [CommRing R] [Finite (MaximalSpectrum R)] [PreconnectedSpace (PrimeSpectrum R)]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M] [Module.Flat R M] :
    Module.Free R M := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have : Subsingleton M := Module.subsingleton R M
    exact Module.Free.of_subsingleton R M
  · obtain ⟨p₀⟩ : Nonempty (PrimeSpectrum R) := inferInstance
    refine Module.free_of_flat_of_finrank_eq R M (Module.rankAtStalk M p₀) fun P ↦ ?_
    rw [Module.finrank_quotient_tensorProduct_eq_rankAtStalk]
    exact (Module.isLocallyConstant_rankAtStalk (R := R) (M := M)).apply_eq_of_preconnectedSpace
      P.toPrimeSpectrum p₀

end TauCeti
