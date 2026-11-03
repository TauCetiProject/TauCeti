/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Kernel
public import TauCeti.RingTheory.Grassmannian.HopfIdeal

/-!
# The quotient Hopf algebra at a point of the Hopf-ideal locus

Let `H` be a Hopf algebra over a commutative ring `R`, and let `N` be a point of the Grassmannian
functor `G(k, A ⊗[R] H; A)` lying on the Hopf-ideal locus, that is, with
`N.hopfIdealLocus = ⊥` (`Module.Grassmannian.hopfIdealLocus_eq_bot_iff`). This file packages the
quotient of `A ⊗[R] H` by `N` as an `A`-Hopf algebra, finite projective of constant rank `k` over
`A`, and proves that its formation commutes with arbitrary base change as a bialgebra. For
commutative `H`, its spectrum is the closed subgroup scheme of the base change of `Spec H` to
`Spec A` attached to `N`, finite locally free of rank `k`, and the base change statement says that
pulling it back along `Spec B ⟶ Spec A` gives the subgroup scheme attached to the base change of
`N`. These are the affine pieces of the universal subgroup over the Hopf-ideal locus.

On the Hopf-ideal locus, `N` is stable under multiplication by `A ⊗[R] H`. The resulting ideal
`N.hopfIdeal hN`, whose underlying `A`-submodule is `N`, is a two-sided Hopf ideal, so Mathlib's
`HopfAlgebra.Quotient` makes the quotient an `A`-Hopf algebra. As an `A`-module the quotient is
the quotient by `N`, hence finite projective of constant rank `k`.

For an `A`-algebra `B`, the base change `map (IsScalarTower.toAlgHom R A B) N` again lies on the
Hopf-ideal locus (`Module.Grassmannian.hopfIdealLocus_map_eq_bot`), and the map
`b ⊗ₜ h ↦ b ⊗ₜ [1 ⊗ₜ h]` induces an isomorphism of `B`-bialgebras from the quotient of `B ⊗[R] H`
by the base change of `N` to `B ⊗[A] ((A ⊗[R] H) ⧸ N)`
(`Module.Grassmannian.quotHopfIdealMapBialgEquiv`). That this map is injective on the quotient is
the description of the base change of `N` as the kernel of `Module.Grassmannian.baseChangeMkQ`
(`Module.Grassmannian.map_toAlgHom_toSubmodule`). For commutative Hopf algebras,
`TauCeti.CommHopfAlgCat.quotientBaseChangeIso` describes the base change of a quotient by a Hopf
ideal inside `B ⊗[A] (A ⊗[R] H)`; here the ambient algebra is `B ⊗[R] H`, where the Grassmannian
functor places the base change of `N`, and `H` need not be commutative.

## Main definitions

* `Module.Grassmannian.hopfIdeal N hN`: a point `N` of the Hopf-ideal locus as a two-sided Hopf
  ideal of `A ⊗[R] H`.
* `Module.Grassmannian.quotHopfIdealMapBialgEquiv`: the formation of the quotient Hopf algebra
  commutes with base change.
* `Module.Grassmannian.hopfIdealLocusEquiv`: the points of the Hopf-ideal locus are the two-sided
  Hopf ideals of `A ⊗[R] H` whose quotient is finite projective of constant rank `k` over `A`.
  Its scheme-level form is `Module.Grassmannian.hopfIdealLocusEquivClosedSubgroupScheme`.

## Main results

* `Module.Grassmannian.hopfIdeal_eq`: `N.hopfIdeal hN` is the unique ideal with underlying
  `A`-submodule `N`.
* `Module.Grassmannian.rankAtStalk_quotient_hopfIdeal`: the quotient Hopf algebra has constant rank
  `k` over `A`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes* (Springer, 1979), §2.1, for closed
  subgroup schemes of affine group schemes as quotients by Hopf ideals.
* [The Stacks Project, Tag 089R](https://stacks.math.columbia.edu/tag/089R), for the Grassmannian
  functor.
-/

public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {k : ℕ} {A B : Type w} [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

variable {H : Type v} [Ring H] [HopfAlgebra R H]

section HopfIdeal

variable (N : G(k, A ⊗[R] H; A)) (hN : N.hopfIdealLocus = ⊥)

/-- A point `N` of the Hopf-ideal locus, as an ideal of `A ⊗[R] H`: on the locus, `N` is stable
under multiplication by `A ⊗[R] H`. It is a two-sided Hopf ideal, so the quotient of `A ⊗[R] H` by
it is an `A`-Hopf algebra which is finite projective of constant rank `k` over `A`. -/
noncomputable def hopfIdeal : Ideal (A ⊗[R] H) where
  __ := N.toSubmodule.toAddSubmonoid
  smul_mem' c y hy := by
    obtain ⟨I, hI, -, -⟩ := (hopfIdealLocus_eq_bot_iff N).1 hN
    rw [← hI] at hy ⊢
    exact I.mul_mem_left c hy

/-- The underlying `A`-submodule of `N.hopfIdeal hN` is `N`. -/
@[simp]
theorem restrictScalars_hopfIdeal : (N.hopfIdeal hN).restrictScalars A = N.toSubmodule :=
  (rfl)

/-- The elements of `N.hopfIdeal hN` are the vectors of `N`. -/
@[simp]
theorem mem_hopfIdeal {x : A ⊗[R] H} : x ∈ N.hopfIdeal hN ↔ x ∈ N.toSubmodule :=
  Iff.rfl

/-- `N.hopfIdeal hN` is the only ideal of `A ⊗[R] H` with underlying `A`-submodule `N`. -/
theorem hopfIdeal_eq {I : Ideal (A ⊗[R] H)} (hI : I.restrictScalars A = N.toSubmodule) :
    N.hopfIdeal hN = I :=
  Submodule.restrictScalars_injective A _ _ ((restrictScalars_hopfIdeal N hN).trans hI.symm)

/-- On the Hopf-ideal locus, the ideal of `A ⊗[R] H` generated by `N` is `N.hopfIdeal hN`. -/
theorem span_toSubmodule_eq_hopfIdeal :
    Ideal.span (N.toSubmodule : Set (A ⊗[R] H)) = N.hopfIdeal hN :=
  Ideal.span_eq (N.hopfIdeal hN)

instance : (N.hopfIdeal hN).IsTwoSided := by
  obtain ⟨I, hI, hTwo, -⟩ := (hopfIdealLocus_eq_bot_iff N).1 hN
  rw [hopfIdeal_eq N hN hI]
  exact hTwo

instance : (N.hopfIdeal hN).IsHopfIdeal A := by
  obtain ⟨I, hI, -, hHopf⟩ := (hopfIdealLocus_eq_bot_iff N).1 hN
  rw [hopfIdeal_eq N hN hI]
  exact hHopf

/-- As an `A`-module, the quotient by `N.hopfIdeal hN` is the quotient by `N`. -/
noncomputable def quotientEquivQuotientHopfIdeal :
    ((A ⊗[R] H) ⧸ N.toSubmodule) ≃ₗ[A] (A ⊗[R] H) ⧸ N.hopfIdeal hN :=
  (Submodule.quotEquivOfEq _ _ (restrictScalars_hopfIdeal N hN).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv A (N.hopfIdeal hN))

/-- `quotientEquivQuotientHopfIdeal` sends the class of `x` modulo `N` to its class modulo
`N.hopfIdeal hN`. -/
@[simp]
theorem quotientEquivQuotientHopfIdeal_mk (x : A ⊗[R] H) :
    quotientEquivQuotientHopfIdeal N hN (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk (N.hopfIdeal hN) x :=
  (rfl)

instance : Module.Finite A ((A ⊗[R] H) ⧸ N.hopfIdeal hN) :=
  Module.Finite.equiv (quotientEquivQuotientHopfIdeal N hN)

instance : Module.Projective A ((A ⊗[R] H) ⧸ N.hopfIdeal hN) :=
  Module.Projective.of_equiv (quotientEquivQuotientHopfIdeal N hN)

/-- The quotient Hopf algebra at a point of the Hopf-ideal locus has constant rank `k`. -/
theorem rankAtStalk_quotient_hopfIdeal (p : PrimeSpectrum A) :
    rankAtStalk (R := A) ((A ⊗[R] H) ⧸ N.hopfIdeal hN) p = k := by
  rw [← rankAtStalk_eq_of_equiv (quotientEquivQuotientHopfIdeal N hN)]
  exact N.rankAtStalk_eq p

end HopfIdeal

section HopfIdealLocusEquiv

/-- The points of the Hopf-ideal locus of `G(k, A ⊗[R] H; A)` are the two-sided Hopf ideals of
`A ⊗[R] H` whose quotient is finite projective of constant rank `k` over `A`. A point `N` goes to
`N.hopfIdeal hN`, and a Hopf ideal `I` goes to its underlying `A`-submodule. -/
noncomputable def hopfIdealLocusEquiv :
    {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥} ≃
      {I : TauCeti.HopfIdeal A (A ⊗[R] H) //
        Module.Finite A ((A ⊗[R] H) ⧸ I.toIdeal) ∧ Module.Projective A ((A ⊗[R] H) ⧸ I.toIdeal) ∧
          ∀ p, rankAtStalk (R := A) ((A ⊗[R] H) ⧸ I.toIdeal) p = k} where
  toFun N := ⟨TauCeti.HopfIdeal.ofIsHopfIdeal A (N.1.hopfIdeal N.2), by
    rw [TauCeti.HopfIdeal.ofIsHopfIdeal_toIdeal]
    exact ⟨inferInstance, inferInstance, rankAtStalk_quotient_hopfIdeal N.1 N.2⟩⟩
  invFun I :=
    have := I.2.1
    have := I.2.2.1
    ⟨{ toSubmodule := I.1.toIdeal.restrictScalars A
       finite_quotient :=
         Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv A I.1.toIdeal).symm
       projective_quotient :=
         Module.Projective.of_equiv (Submodule.Quotient.restrictScalarsEquiv A I.1.toIdeal).symm
       rankAtStalk_eq p := by
         rw [rankAtStalk_eq_of_equiv (Submodule.Quotient.restrictScalarsEquiv A I.1.toIdeal)]
         exact I.2.2.2 p },
      (hopfIdealLocus_eq_bot_iff _).2 ⟨I.1.toIdeal, rfl, inferInstance, inferInstance⟩⟩
  left_inv N := Subtype.ext <| Grassmannian.ext <| by
    dsimp only
    rw [TauCeti.HopfIdeal.ofIsHopfIdeal_toIdeal, restrictScalars_hopfIdeal]
  right_inv I := Subtype.ext <| TauCeti.HopfIdeal.ext fun _ ↦ by
    rw [TauCeti.HopfIdeal.mem_ofIsHopfIdeal, mem_hopfIdeal, Submodule.restrictScalars_mem,
      TauCeti.HopfIdeal.mem_toIdeal]

/-- `hopfIdealLocusEquiv` sends a point `N` of the Hopf-ideal locus to `N.hopfIdeal hN`. -/
@[simp]
theorem hopfIdealLocusEquiv_apply_coe (N : {N : G(k, A ⊗[R] H; A) // N.hopfIdealLocus = ⊥}) :
    (hopfIdealLocusEquiv N).1 = TauCeti.HopfIdeal.ofIsHopfIdeal A (N.1.hopfIdeal N.2) :=
  (rfl)

/-- `hopfIdealLocusEquiv.symm` sends a Hopf ideal to its underlying `A`-submodule. -/
@[simp]
theorem hopfIdealLocusEquiv_symm_apply_toSubmodule
    (I : {I : TauCeti.HopfIdeal A (A ⊗[R] H) //
      Module.Finite A ((A ⊗[R] H) ⧸ I.toIdeal) ∧ Module.Projective A ((A ⊗[R] H) ⧸ I.toIdeal) ∧
        ∀ p, rankAtStalk (R := A) ((A ⊗[R] H) ⧸ I.toIdeal) p = k}) :
    (hopfIdealLocusEquiv.symm I).1.toSubmodule = I.1.toIdeal.restrictScalars A := by
  rfl

end HopfIdealLocusEquiv

section BaseChange

variable {N : G(k, A ⊗[R] H; A)}

variable (hN : N.hopfIdealLocus = ⊥) (B) [Algebra A B] [IsScalarTower R A B]

/-- The algebra map `B ⊗[R] H → B ⊗[A] ((A ⊗[R] H) ⧸ N.hopfIdeal hN)` sending `b ⊗ₜ h` to
`b ⊗ₜ [1 ⊗ₜ h]`. -/
private noncomputable def baseChangeAlgHom :
    B ⊗[R] H →ₐ[B] B ⊗[A] ((A ⊗[R] H) ⧸ N.hopfIdeal hN) :=
  AlgHom.liftEquiv R B H _ ((Algebra.TensorProduct.includeRight.restrictScalars R).comp
    (((Ideal.Quotient.mkₐ A (N.hopfIdeal hN)).restrictScalars R).comp
      Algebra.TensorProduct.includeRight))

private theorem baseChangeAlgHom_tmul (b : B) (h : H) :
    baseChangeAlgHom B hN (b ⊗ₜ h) = b ⊗ₜ Ideal.Quotient.mk (N.hopfIdeal hN) (1 ⊗ₜ h) := by
  simp [baseChangeAlgHom, smul_tmul']

private theorem baseChangeAlgHom_apply (x : B ⊗[R] H) :
    baseChangeAlgHom B hN x = (quotientEquivQuotientHopfIdeal N hN).baseChange A B _ _
      (baseChangeMkQ B N.toSubmodule x) := by
  induction x using TensorProduct.inductionOn with
  | tmul b h => simp [baseChangeAlgHom_tmul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

private theorem baseChangeAlgHom_surjective : Function.Surjective (baseChangeAlgHom B hN) := by
  intro z
  obtain ⟨x, hx⟩ := baseChangeMkQ_surjective (B := B) N.toSubmodule
    (((quotientEquivQuotientHopfIdeal N hN).baseChange A B _ _).symm z)
  exact ⟨x, by rw [baseChangeAlgHom_apply, hx, LinearEquiv.apply_symm_apply]⟩

private theorem ker_baseChangeAlgHom :
    RingHom.ker (baseChangeAlgHom B hN) =
      (map (IsScalarTower.toAlgHom R A B) N).hopfIdeal (hopfIdealLocus_map_eq_bot hN _) := by
  ext x
  rw [RingHom.mem_ker, mem_hopfIdeal, map_toAlgHom_toSubmodule, LinearMap.mem_ker,
    baseChangeAlgHom_apply, LinearEquiv.map_eq_zero_iff]

/-- The quotient of `B ⊗[R] H` by the base change of `N`, as a `B`-algebra, is the base change of
the quotient of `A ⊗[R] H` by `N`. -/
private noncomputable def quotHopfIdealMapAlgEquiv :
    ((B ⊗[R] H) ⧸ (map (IsScalarTower.toAlgHom R A B) N).hopfIdeal
      (hopfIdealLocus_map_eq_bot hN _)) ≃ₐ[B] B ⊗[A] ((A ⊗[R] H) ⧸ N.hopfIdeal hN) :=
  (Ideal.quotientEquivAlgOfEq B (ker_baseChangeAlgHom B hN).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (baseChangeAlgHom_surjective B hN))

private theorem quotHopfIdealMapAlgEquiv_mk (x : B ⊗[R] H) :
    quotHopfIdealMapAlgEquiv B hN (Ideal.Quotient.mk _ x) = baseChangeAlgHom B hN x :=
  (rfl)

private theorem counitAlgHom_comp_quotHopfIdealMapAlgEquiv :
    (Bialgebra.counitAlgHom B _).comp (quotHopfIdealMapAlgEquiv B hN).toAlgHom =
    Bialgebra.counitAlgHom B _ := by
  refine Ideal.Quotient.algHom_ext B ?_
  ext h
  simp [quotHopfIdealMapAlgEquiv_mk, baseChangeAlgHom_tmul]

private theorem map_comp_comulAlgHom_quotHopfIdealMapAlgEquiv :
    (Algebra.TensorProduct.map (quotHopfIdealMapAlgEquiv B hN).toAlgHom
      (quotHopfIdealMapAlgEquiv B hN).toAlgHom).comp (Bialgebra.comulAlgHom B _) =
    (Bialgebra.comulAlgHom B _).comp (quotHopfIdealMapAlgEquiv B hN).toAlgHom := by
  refine Ideal.Quotient.algHom_ext B ?_
  ext h
  simp only [AlgHom.coe_comp, AlgHom.coe_restrictScalars', Function.comp_apply,
    Algebra.TensorProduct.includeRight_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom,
    Bialgebra.comulAlgHom_apply, quotHopfIdealMapAlgEquiv_mk, baseChangeAlgHom_tmul,
    Bialgebra.Quotient.comul_mk, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
  | tmul h₁ h₂ => simp [quotHopfIdealMapAlgEquiv_mk, baseChangeAlgHom_tmul]
  | add s t hs ht => simp only [tmul_add, map_add, hs, ht]

/-- **The quotient Hopf algebra commutes with base change.** For a point `N` of the Hopf-ideal
locus and an `A`-algebra `B`, the quotient of `B ⊗[R] H` by the base change of `N` is isomorphic,
as a `B`-bialgebra, to the base change `B ⊗[A] ((A ⊗[R] H) ⧸ N)` of the quotient Hopf algebra,
by the map sending the class of `b ⊗ₜ h` to `b ⊗ₜ [1 ⊗ₜ h]`. -/
noncomputable def quotHopfIdealMapBialgEquiv :
    ((B ⊗[R] H) ⧸ (map (IsScalarTower.toAlgHom R A B) N).hopfIdeal
      (hopfIdealLocus_map_eq_bot hN _)) ≃ₐc[B] B ⊗[A] ((A ⊗[R] H) ⧸ N.hopfIdeal hN) :=
  .ofAlgEquiv (quotHopfIdealMapAlgEquiv B hN) (counitAlgHom_comp_quotHopfIdealMapAlgEquiv B hN)
    (map_comp_comulAlgHom_quotHopfIdealMapAlgEquiv B hN)

private theorem quotHopfIdealMapBialgEquiv_mk (x : B ⊗[R] H) :
    quotHopfIdealMapBialgEquiv B hN (Ideal.Quotient.mk _ x) = baseChangeAlgHom B hN x :=
  (rfl)

/-- `quotHopfIdealMapBialgEquiv` sends the class of `b ⊗ₜ h` to `b ⊗ₜ [1 ⊗ₜ h]`. -/
@[simp]
theorem quotHopfIdealMapBialgEquiv_mk_tmul (b : B) (h : H) :
    quotHopfIdealMapBialgEquiv B hN (Ideal.Quotient.mk _ (b ⊗ₜ h)) =
      b ⊗ₜ Ideal.Quotient.mk (N.hopfIdeal hN) (1 ⊗ₜ h) := by
  rw [quotHopfIdealMapBialgEquiv_mk, baseChangeAlgHom_tmul]

/-- The inverse of `quotHopfIdealMapBialgEquiv` sends `b ⊗ₜ [x]` to `b` times the class of the
image of `x` in `B ⊗[R] H`. -/
@[simp]
theorem quotHopfIdealMapBialgEquiv_symm_tmul_mk (b : B) (x : A ⊗[R] H) :
    (quotHopfIdealMapBialgEquiv B hN).symm (b ⊗ₜ Ideal.Quotient.mk (N.hopfIdeal hN) x) =
      b • Ideal.Quotient.mk _ ((IsScalarTower.toAlgHom R A B).toLinearMap.rTensor H x) := by
  apply EquivLike.injective (quotHopfIdealMapBialgEquiv B hN)
  rw [BialgEquiv.apply_symm_apply, map_smul, quotHopfIdealMapBialgEquiv_mk, baseChangeAlgHom_apply,
    baseChangeMkQ_rTensor]
  simp [smul_tmul']

end BaseChange

end Module.Grassmannian
