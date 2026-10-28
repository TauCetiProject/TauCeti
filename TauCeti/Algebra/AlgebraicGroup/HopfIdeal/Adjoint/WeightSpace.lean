/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Adjoint.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Torus
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace

/-!
# Adjoint weights of a closed subgroup with a weight torus

A torus map to a closed subgroup of `GLₙ` whose ambient map is diagonal with weights `w`
acts on tangent-matrix entry `(i,j)` through `w i - w j`. Testing the universal torus
point detects exactly the entries allowed in an adjoint weight space. The derivation
criterion needs no smoothness assumption; the comodule criterion assumes that the
augmentation cotangent module is finite projective.

The argument factors the matrix computations of
`TauCeti.SpecialLinear.adDerivation_universalDiagonalTorus_eq_iff` and its comodule
criterion through the injective closed-subgroup differential. This supplies the common
entrywise criterion used in classical pinnings.

The comodule criterion needs the torus coordinates indexed in the universe of the base ring.
`mem_adjointWeightSpace_iff_of_weightTorusCoordinateBialgHom` states it for coordinates indexed
by any finite type over a base ring in any universe, as for the `Fin r` weight tori of the
explicit Chevalley carriers, and `adjointWeightSpace_eq_bot_of_weightTorusCoordinateBialgHom`
deduces that a weight space vanishes when the generic matrix entries of that weight vanish in the
quotient.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§21.1 and 24.6.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

open CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.HopfIdeal

universe u

noncomputable section

variable {R : Type u} [CommRing R] {n : ℕ} {σ : Type u} [Fintype σ]
variable (I : HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n))
variable (w : Fin n → σ → ℤ)
variable (π : (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) →ₐc[R]
  MonoidAlgebra R (Multiplicative (σ →₀ ℤ)))
variable (hπ : π.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) =
  (GeneralLinear.weightTorusCoordinateMap w).hom)

include hπ

private theorem ambientCounitPoint_weightTorus {B : Type*} [CommRing B] [Algebra R B]
    (s : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] B)) :
    GeneralLinear.counitPointsMulEquiv n
      (BialgHom.mapDomain (A := Bialgebra.CounitAlgebra R
        (GeneralLinear.coordinateHopfAlgebra R n) B)
        (Bialgebra.Quotient.mkBialgHom I.toIdeal)
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B
          (toConv (s.ofConv.comp π.toAlgHom)))) =
      diagGL (fun i => DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (w i))) := by
  rw [GeneralLinear.counitPointsMulEquiv_eq_pointsMulEquiv]
  have hpoint :
      AlgHom.mapValue
          (Bialgebra.CounitAlgebra.algEquivSelf R
            (GeneralLinear.coordinateHopfAlgebra R n) B).toAlgHom
          (BialgHom.mapDomain (A := Bialgebra.CounitAlgebra R
            (GeneralLinear.coordinateHopfAlgebra R n) B)
            (Bialgebra.Quotient.mkBialgHom I.toIdeal)
            (Derivation.pointInCounitAlgebra
              (H := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B
              (toConv (s.ofConv.comp π.toAlgHom)))) =
        toConv (s.ofConv.comp (GeneralLinear.weightTorusCoordinateMap w).hom.toAlgHom) := by
    apply WithConv.ofConv_injective
    ext x
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    -- `mapDomain` returns the ambient-indexed counit algebra, while the point uses
    -- the quotient-indexed one. The application rules erase these coefficient indexings.
    erw [Bialgebra.CounitAlgebra.algEquivSelf_apply, BialgHom.mapDomain_apply_apply,
      Derivation.pointInCounitAlgebra_apply]
    rw [ofConv_toConv, AlgHom.comp_apply]
    exact congrArg s.ofConv (BialgHom.congr_fun hπ x)
  rw [hpoint]
  have hdiag := GeneralLinear.pointsMulEquiv_mapPointsFunctor_weightTorusCoordinateMap w
    (CommAlgCat.of R B) s
  -- The categorical point uses `CommAlgCat.of R B`; expose its algebra-hom presentation.
  erw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hdiag
  simpa only [SplitTorus.charOfPoint_weightCharacter] using hdiag

/-- A weight-torus point scales each entry of the ambient tangent matrix of a closed
subgroup by the difference of its two standard weights. -/
theorem tangentMatrix_adDerivation_weightTorus_apply
    {B : Type*} [CommRing B] [Algebra R B]
    (s : WithConv (MonoidAlgebra R (Multiplicative (σ →₀ ℤ)) →ₐ[R] B))
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B))
    (i j : Fin n) :
    GeneralLinear.tangentMatrix n (quotientLieHom I
      (Derivation.adDerivation B
        (Derivation.pointInCounitAlgebra
          (H := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) B
          (toConv (s.ofConv.comp π.toAlgHom))) d)) i j =
      (DiagonalizableGroup.charOfPoint s.ofConv
        (SplitTorus.weightCharacter (w i - w j)) : B) *
        GeneralLinear.tangentMatrix n (quotientLieHom I d) i j := by
  rw [quotientLieHom_adDerivation,
    GeneralLinear.tangentMatrix_adDerivation_apply_of_diagGL
      (ambientCounitPoint_weightTorus I w π hπ s)]
  rw [SplitTorus.charOfPoint_weightCharacter, SplitTorus.charOfPoint_weightCharacter,
    SplitTorus.charOfPoint_weightCharacter, torusCharacter_sub, div_eq_mul_inv, Units.val_mul]
  ring

/-- At the universal weight-torus point, a closed-subgroup tangent-matrix entry is
multiplied by its integral character in the group-algebra basis. -/
theorem tangentMatrix_adDerivation_universalWeightTorus_apply
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) R))
    (i j : Fin n) :
    GeneralLinear.tangentMatrix n (quotientLieHom I
      (Derivation.adDerivation (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
        (Derivation.pointInCounitAlgebra
          (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
          (toConv π.toAlgHom)) (Derivation.mapValue (Algebra.ofId R _) d))) i j =
      MonoidAlgebra.single (SplitTorus.weightCharacter (w i - w j))
        (GeneralLinear.tangentMatrix n (quotientLieHom I d) i j) := by
  have h := tangentMatrix_adDerivation_weightTorus_apply I w π hπ
    (toConv (AlgHom.id R _)) (Derivation.mapValue (Algebra.ofId R _) d) i j
  rw [ofConv_toConv, AlgHom.id_comp] at h
  rw [h, quotientLieHom_mapValue, GeneralLinear.tangentMatrix_mapValue, Matrix.map_apply,
    DiagonalizableGroup.charOfPoint_apply_coe, AlgHom.id_apply, Algebra.ofId_apply]
  rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]

/-- A closed-subgroup tangent vector is an eigenvector at the universal weight-torus
point exactly when entries of every other character vanish. -/
theorem adDerivation_universalWeightTorus_eq_iff
    (α : Multiplicative (σ →₀ ℤ))
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) R)) :
    Derivation.adDerivation (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
        (Derivation.pointInCounitAlgebra
          (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (σ →₀ ℤ))))
          (toConv π.toAlgHom)) (Derivation.mapValue (Algebra.ofId R _) d) =
      MonoidAlgebra.single α (1 : R) • Derivation.mapValue (Algebra.ofId R _) d ↔
      ∀ i j : Fin n, SplitTorus.weightCharacter (w i - w j) ≠ α →
        GeneralLinear.tangentMatrix n (quotientLieHom I d) i j = 0 := by
  let K := MonoidAlgebra R (Multiplicative (σ →₀ ℤ))
  have hentry (i j : Fin n) :
      GeneralLinear.tangentMatrix n (quotientLieHom I
        (MonoidAlgebra.single α (1 : R) • Derivation.mapValue (Algebra.ofId R K) d)) i j =
        MonoidAlgebra.single α (GeneralLinear.tangentMatrix n (quotientLieHom I d) i j) := by
    rw [map_smul, map_smul, Matrix.smul_apply, smul_eq_mul,
      quotientLieHom_mapValue, GeneralLinear.tangentMatrix_mapValue, Matrix.map_apply,
      Algebra.ofId_apply]
    rw [mul_comm, ← MonoidAlgebra.of_apply, ← MonoidAlgebra.single_eq_algebraMap_mul_of]
  constructor
  · intro h i j hij
    have he := congrArg (fun e => GeneralLinear.tangentMatrix n (quotientLieHom I e) i j) h
    rw [tangentMatrix_adDerivation_universalWeightTorus_apply I w π hπ, hentry] at he
    by_contra hne
    exact hij (MonoidAlgebra.single_left_injective hne he)
  · intro h
    apply quotientLieHom_injective I
    apply (GeneralLinear.tangentLinearEquivMatrix (R := R) (B := K) n).injective
    rw [GeneralLinear.tangentLinearEquivMatrix_apply,
      GeneralLinear.tangentLinearEquivMatrix_apply]
    ext i j
    rw [tangentMatrix_adDerivation_universalWeightTorus_apply I w π hπ, hentry]
    by_cases hij : SplitTorus.weightCharacter (w i - w j) = α
    · rw [hij]
    · simp [h i j hij]

variable [Module.Finite R
  (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))]

/-- For a closed subgroup with a weight-torus factorization, membership in the actual
adjoint comodule weight space is equivalent to vanishing of entries of every other weight. -/
theorem mem_adjointWeightSpace_iff_of_weightTorus
    (α : Multiplicative (σ →₀ ℤ))
    (x : Module.Dual R
      (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))) :
    x ∈ Derivation.adjointWeightSpace π α ↔
      ∀ i j : Fin n, SplitTorus.weightCharacter (w i - w j) ≠ α →
        GeneralLinear.tangentMatrix n
          (quotientLieHom I (Derivation.cotangentLinearEquiv (B := R) x)) i j = 0 := by
  rw [Derivation.mem_adjointWeightSpace_iff_universalPointAction]
  let K := MonoidAlgebra R (Multiplicative (σ →₀ ℤ))
  rw [← (Derivation.tangentScalarExtensionEquiv
    (R := R) (A := GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) (B := K)).injective.eq_iff]
  rw [Derivation.tangentScalarExtensionEquiv_adjointAction (CommAlgCat.of R K)
      (toConv π.toAlgHom), Derivation.tangentScalarExtensionEquiv_tmul, one_smul,
    Derivation.tangentScalarExtensionEquiv_tmul,
    adDerivation_universalWeightTorus_eq_iff I w π hπ]

end

section SmallWeights

/-! ### Torus coordinates in any universe

The criterion above indexes the torus coordinates by a type in the universe of the base ring,
which the universal torus point requires. For a finite index type in any universe, relabelling
along an equivalence with `ULift (Fin r)` moves the characters into that universe without
changing them. -/

noncomputable section

universe v

variable {R : Type u} [CommRing R] {n : ℕ} {τ : Type v}
variable (I : HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n))

/-- Relabelling the torus coordinates along an equivalence identifies the two character
lattices. -/
private def relabelCharacterEquiv {κ : Type*} (e : τ ≃ κ) :
    Multiplicative (τ →₀ ℤ) ≃* Multiplicative (κ →₀ ℤ) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr e)

private theorem relabelCharacterEquiv_single {κ : Type*} (e : τ ≃ κ)
    (α : Multiplicative (τ →₀ ℤ)) :
    MonoidAlgebra.domCongrBialgEquiv R R (relabelCharacterEquiv e) (MonoidAlgebra.single α 1) =
      MonoidAlgebra.single (relabelCharacterEquiv e α) 1 := by
  simp only [MonoidAlgebra.domCongrBialgEquiv, BialgEquiv.ofAlgEquiv_apply]
  exact MonoidAlgebra.domCongr_single (R := R) (A := R) (relabelCharacterEquiv e) α 1

private theorem relabelCharacterEquiv_weightCharacter [Fintype τ] {κ : Type*} [Fintype κ]
    (e : τ ≃ κ) (v : τ → ℤ) :
    relabelCharacterEquiv e (SplitTorus.weightCharacter v) =
      SplitTorus.weightCharacter (fun i : κ ↦ v (e.symm i)) := by
  apply Multiplicative.toAdd.injective
  ext i
  simp [relabelCharacterEquiv, Finsupp.domCongr]

private theorem relabel_weightTorusCoordinateBialgHom [Finite τ] {κ : Type u} [Finite κ]
    (e : τ ≃ κ) (w : Fin n → τ → ℤ) :
    (MonoidAlgebra.domCongrBialgEquiv R R (relabelCharacterEquiv e)).toBialgHom.comp
        (GeneralLinear.weightTorusCoordinateBialgHom (S := R) w) =
      (GeneralLinear.weightTorusCoordinateMap (fun a (i : κ) ↦ w a (e.symm i))).hom := by
  let _ : Fintype τ := Fintype.ofFinite τ
  let _ : Fintype κ := Fintype.ofFinite κ
  apply GeneralLinear.coordinateHopfAlgebra_bialgHom_ext R n
  intro a b
  rw [BialgHom.comp_apply, GeneralLinear.weightTorusCoordinateBialgHom_X,
    GeneralLinear.weightTorusCoordinateMap_X]
  split_ifs with hab
  · -- The direct torus map uses the finitely supported representative of its character;
    -- the bialgebra equivalence acts through the same underlying function.
    change MonoidAlgebra.domCongrBialgEquiv R R (relabelCharacterEquiv e)
        (MonoidAlgebra.single
          (Multiplicative.ofAdd (Finsupp.equivFunOnFinite.symm (w a))) 1) = _
    rw [relabelCharacterEquiv_single]
    congr 1
    rw [← SplitTorus.weightCharacter_coe, ← SplitTorus.weightCharacter_coe,
      Finsupp.coe_equivFunOnFinite_symm, Finsupp.coe_equivFunOnFinite_symm]
    exact relabelCharacterEquiv_weightCharacter e (w a)
  · exact map_zero _

variable [Fintype τ]
variable [Module.Finite R
  (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))]
variable [Module.Projective R
  (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))]

/-- `mem_adjointWeightSpace_iff_of_weightTorus` for a weight torus with coordinates indexed by
any finite type, over a base ring in any universe: membership in the adjoint weight space of `α`
is equivalent to vanishing of every tangent-matrix entry whose weight difference is not `α`. -/
theorem mem_adjointWeightSpace_iff_of_weightTorusCoordinateBialgHom (w : Fin n → τ → ℤ)
    (π : (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) →ₐc[R]
      MonoidAlgebra R (Multiplicative (τ →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) w)
    (α : Multiplicative (τ →₀ ℤ))
    (x : Module.Dual R
      (Bialgebra.CotangentSpace R (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal))) :
    x ∈ Derivation.adjointWeightSpace π α ↔
      ∀ i j : Fin n, SplitTorus.weightCharacter (w i - w j) ≠ α →
        GeneralLinear.tangentMatrix n
          (quotientLieHom I (Derivation.cotangentLinearEquiv (B := R) x)) i j = 0 := by
  let e : τ ≃ ULift.{u} (Fin (Fintype.card τ)) := (Fintype.equivFin τ).trans Equiv.ulift.symm
  let π' := (MonoidAlgebra.domCongrBialgEquiv R R (relabelCharacterEquiv e)).toBialgHom.comp π
  have hπ' : π'.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap (fun a i ↦ w a (e.symm i))).hom := by
    rw [BialgHom.comp_assoc, hπ, relabel_weightTorusCoordinateBialgHom]
  rw [← Derivation.adjointWeightSpace_domCongr (relabelCharacterEquiv e) π α,
    mem_adjointWeightSpace_iff_of_weightTorus I _ π' hπ']
  have hchar (a b : Fin n) :
      SplitTorus.weightCharacter ((fun i ↦ w a (e.symm i)) - fun i ↦ w b (e.symm i)) =
        relabelCharacterEquiv e (SplitTorus.weightCharacter (w a - w b)) :=
    (relabelCharacterEquiv_weightCharacter e (w a - w b)).symm
  simp only [hchar, ne_eq, (relabelCharacterEquiv e).injective.eq_iff]

/-- **Vanishing adjoint weight spaces from vanishing coordinates.** If every generic matrix entry
whose weight difference is `α` vanishes in the quotient coordinate algebra, the adjoint weight
space of `α` is zero. -/
theorem adjointWeightSpace_eq_bot_of_weightTorusCoordinateBialgHom (w : Fin n → τ → ℤ)
    (π : (GeneralLinear.coordinateHopfAlgebra R n ⧸ I.toIdeal) →ₐc[R]
      MonoidAlgebra R (Multiplicative (τ →₀ ℤ)))
    (hπ : π.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) w)
    (α : Multiplicative (τ →₀ ℤ))
    (h : ∀ i j : Fin n, SplitTorus.weightCharacter (w i - w j) = α →
      Bialgebra.Quotient.mkBialgHom (R := R) I.toIdeal (GeneralLinear.genericMatrix R n i j) = 0) :
    Derivation.adjointWeightSpace π α = ⊥ := by
  classical
  -- A weight vector has tangent matrix supported on the entries of weight difference `α`, and a
  -- tangent vector kills the coordinates that vanish in the quotient.
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  have hentry := (mem_adjointWeightSpace_iff_of_weightTorusCoordinateBialgHom I w π hπ α x).mp hx
  apply (Derivation.cotangentLinearEquiv (B := R)).injective
  apply quotientLieHom_injective I
  apply (GeneralLinear.tangentLinearEquivMatrix n).injective
  simp only [GeneralLinear.tangentLinearEquivMatrix_apply]
  ext i j
  simp only [map_zero, Matrix.zero_apply]
  by_cases hij : SplitTorus.weightCharacter (w i - w j) = α
  · have hzero := h i j hij
    rw [GeneralLinear.genericMatrix_apply] at hzero
    have hqzero : Ideal.Quotient.mkₐ R I.toIdeal
        ((GeneralLinear.coordinateHopfAlgebraAlgEquiv R n)
          ((GeneralLinear.coordinateRingMap R n) (MvPolynomial.X (i, j)))) = 0 := by
      simpa only [Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk] using hzero
    simp only [GeneralLinear.tangentMatrix_apply, quotientLieHom_apply_apply, hqzero, map_zero]
    -- The tangent vector is evaluated through the counit-algebra identification, which
    -- preserves zero.
    exact map_zero _
  · exact hentry i j hij

end

end SmallWeights

section

variable {R : Type u} [CommRing R] {n : ℕ} {σ : Type u} [Fintype σ]

/-- For a Hopf algebra presented as a quotient of the coordinate algebra of `GLₙ`,
adjoint weight-space membership is equivalent to vanishing of the ambient tangent-matrix
entries of every other weight. The quotient map may be supplied as a named morphism. -/
theorem mem_adjointWeightSpace_iff_of_weightTorus_of_eq
    (I : HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n)) (w : Fin n → σ → ℤ)
    {G : CommHopfAlgCat R}
    (hG : G = CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra R n) I)
    (q : GeneralLinear.coordinateHopfAlgebra R n ⟶ G)
    (hq : q ≫ (eqToIso hG).hom =
      CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra R n) I)
    (π : G ⟶ (DiagonalizableGroup.coordinateRing R (SplitTorus.characterGroup σ)).obj)
    (hπ : q ≫ π = GeneralLinear.weightTorusCoordinateMap (R := R) w)
    [Module.Finite R (Bialgebra.CotangentSpace R G)]
    [Module.Projective R (Bialgebra.CotangentSpace R G)]
    (α : Multiplicative (σ →₀ ℤ)) (x : Module.Dual R (Bialgebra.CotangentSpace R G)) :
    x ∈ Derivation.adjointWeightSpace π.hom α ↔
      ∀ a b, SplitTorus.weightCharacter (w a - w b) ≠ α →
        GeneralLinear.tangentMatrix n
          (derivationComp (B := R) q.hom (Derivation.cotangentLinearEquiv (B := R) x)) a b = 0 := by
  subst hG
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id] at hq
  rw [hq] at hπ ⊢
  rw [CommHopfAlgCat.hom_mkQuotient]
  have hπ' : π.hom.comp (Bialgebra.Quotient.mkBialgHom I.toIdeal) =
      (GeneralLinear.weightTorusCoordinateMap (R := R) w).hom := by
    rw [← CommHopfAlgCat.hom_mkQuotient, ← _root_.CommHopfAlgCat.hom_comp, hπ]
  simpa only [quotientLieHom_apply] using
    mem_adjointWeightSpace_iff_of_weightTorus I w π.hom hπ' α x

end

end TauCeti.HopfIdeal
