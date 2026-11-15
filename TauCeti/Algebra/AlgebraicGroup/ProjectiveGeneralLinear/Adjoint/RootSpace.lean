/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.RootSubgroup.Differential
public import TauCeti.Algebra.AlgebraicGroup.ProjectiveGeneralLinear.DiagonalTorus.RootDatum
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Adjoint.WeightSpace

/-!
# Adjoint root spaces of the projective general linear group

Relative to the normalized diagonal torus of `PGL_{r+1}`, the nontrivial adjoint
weights are exactly the roots of its adjoint type-A datum. Each root space is the
line given by the differential of the corresponding elementary root subgroup.
No assumption on the characteristic is needed, including when it divides `r+1`.
The statements work over commutative rings with projective augmentation cotangent
space; this hypothesis holds automatically over every field.

The calculation uses the inner-derivation model of the tangent algebra. The ambient
weight criterion from `HopfIdeal.Adjoint.WeightSpace` detects off-diagonal entries
of an inner representative and differences of its diagonal entries. Scalar matrices
act trivially, so this detects the whole root space without dividing by the rank.
The characteristic API follows `SpecialLinear.Adjoint.Comodule`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), §26.3.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.ProjectiveGeneralLinear

universe u

noncomputable section

variable {R : Type u} [CommRing R] {r : ℕ}

private theorem weightCharacter_diagonalTorusWeight
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    SplitTorus.weightCharacter (diagonalTorusWeight r (finProdFinEquiv p.1)) =
      Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) := by
  apply Multiplicative.toAdd.injective
  ext i
  simp

private theorem weightCharacter_diagonalTorusWeight_self (i : Fin (r + 1)) :
    SplitTorus.weightCharacter (diagonalTorusWeight.{u} r (finProdFinEquiv (i, i))) = 1 := by
  rw [SplitTorus.weightCharacter_eq_one_iff]
  ext j
  simp

private theorem rootCharacter_ne_one
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) ≠ 1 := by
  simpa using (diagonalRootDatum.{u} r).ne_zero p

private theorem weightCharacter_diagonalTorusWeight_eq_root_iff
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) (a b : Fin (r + 1)) :
    SplitTorus.weightCharacter (diagonalTorusWeight.{u} r (finProdFinEquiv (a, b))) =
        Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) ↔
      a = p.1.1 ∧ b = p.1.2 := by
  by_cases hab : a = b
  · subst b
    simp only [weightCharacter_diagonalTorusWeight_self]
    constructor
    · intro h
      exact (rootCharacter_ne_one p h.symm).elim
    · rintro ⟨rfl, h⟩
      exact (p.2 h).elim
  · rw [weightCharacter_diagonalTorusWeight ⟨(a, b), hab⟩]
    constructor
    · intro h
      have hp := (diagonalRootDatum.{u} r).root.injective
        (Multiplicative.ofAdd.injective h)
      exact Prod.mk.inj (congrArg Subtype.val hp)
    · rintro ⟨rfl, rfl⟩
      rfl

/-- The cotangent-dual root vector supplied by the additive parametrization of the
projective elementary root subgroup, with tangent parameter one. -/
def rootVector (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra (r + 1) R)) :=
  (Derivation.cotangentLinearEquiv (R := R)
    (A := coordinateHopfAlgebra (r + 1) R) (B := R)).symm
      (derivationComp (B := R) (rootSubgroupCoordinateMap p.2).hom
        ((AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1))

/-- The normalized root vector acts by commutator with the matrix unit. -/
@[simp]
theorem tangentEnd_cotangentLinearEquiv_rootVector
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    tangentEnd (R := R) (r + 1)
        (Derivation.cotangentLinearEquiv (R := R) (B := R) (rootVector (R := R) p)) =
      LinearMap.mulLeft R (Matrix.single p.1.1 p.1.2 1) -
        LinearMap.mulRight R (Matrix.single p.1.1 p.1.2 1) := by
  rw [rootVector, LinearEquiv.apply_symm_apply, tangentEnd_derivationComp_rootSubgroup,
    LinearEquiv.apply_symm_apply]

/-- The differential of an elementary root subgroup is its additive tangent
parameter times the normalized projective root vector, in the cotangent-dual model. -/
@[simp]
theorem cotangentLinearEquiv_symm_derivationComp_rootSubgroup
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (d : Derivation R (AdditiveGroup.coordinateHopfAlgebra R)
      (Bialgebra.CounitAlgebra R (AdditiveGroup.coordinateHopfAlgebra R) R)) :
    (Derivation.cotangentLinearEquiv (R := R)
      (A := coordinateHopfAlgebra (r + 1) R) (B := R)).symm
        (derivationComp (B := R) (rootSubgroupCoordinateMap (R := R) p.2).hom d) =
      AdditiveGroup.gaTangentLinearEquiv d • rootVector (R := R) p := by
  have hd : d = AdditiveGroup.gaTangentLinearEquiv d •
      (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).symm 1 := by
    apply (AdditiveGroup.gaTangentLinearEquiv (R := R) (B := R)).injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  conv_lhs => rw [hd]
  rw [map_smul, map_smul, rootVector]

/-- The coefficient of a multiple of a root vector is recovered by applying it to
`E_jj` and reading its `(i,j)` entry. -/
@[simp]
theorem tangentEnd_smul_rootVector_apply
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) (c : R) :
    tangentEnd (R := R) (r + 1)
        (Derivation.cotangentLinearEquiv (R := R) (B := R) (c • rootVector (R := R) p))
        (Matrix.single p.1.2 p.1.2 1) p.1.1 p.1.2 = c := by
  rw [map_smul, map_smul, tangentEnd_cotangentLinearEquiv_rootVector]
  simp [p.2.symm]

/-- Multiplication by a projective root vector is injective over every base ring. -/
theorem rootVector_smul_left_injective
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Function.Injective (fun c : R ↦ c • rootVector (R := R) p) := by
  intro a b h
  have he := congrArg (fun x ↦
    tangentEnd (R := R) (r + 1) (Derivation.cotangentLinearEquiv (R := R) (B := R) x)
      (Matrix.single p.1.2 p.1.2 1) p.1.1 p.1.2) h
  rw [tangentEnd_smul_rootVector_apply, tangentEnd_smul_rootVector_apply] at he
  exact he

/-- The normalized projective root vectors are nonzero over a nontrivial base ring. -/
theorem rootVector_ne_zero [Nontrivial R]
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) : rootVector (R := R) p ≠ 0 := by
  intro h
  have he : (1 : R) = 0 := rootVector_smul_left_injective p (by simp [h])
  exact one_ne_zero he

variable [Module.Projective R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra (r + 1) R))]

/-- A tangent vector has torus weight `α` exactly when its ambient matrix entries
of every other character vanish. -/
theorem mem_adjointWeightSpace_iff
    (α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra (r + 1) R))) :
    x ∈ Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom α ↔
      ∀ a b, SplitTorus.weightCharacter (diagonalTorusWeight r a - diagonalTorusWeight r b) ≠ α →
        GeneralLinear.tangentMatrix ((r + 1) * (r + 1))
          (HopfIdeal.quotientLieHom (definingHopfIdeal (r + 1) R)
            (Derivation.cotangentLinearEquiv (R := R) (B := R) x)) a b = 0 := by
  exact HopfIdeal.mem_adjointWeightSpace_iff_of_weightTorus
    (definingHopfIdeal (r + 1) R) (diagonalTorusWeight r)
    (diagonalTorusCoordinateMap r R).hom
    (congrArg (fun f ↦ f.hom) (mkQuotient_comp_diagonalTorusCoordinateMap r R)) α x

private theorem mem_adjointWeightSpace_iff_of_inner
    (α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) (hα : α ≠ 1)
    (x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra (r + 1) R)))
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hX : tangentEnd (R := R) (r + 1) (Derivation.cotangentLinearEquiv (R := R) (B := R) x) =
      LinearMap.mulLeft R X - LinearMap.mulRight R X) :
    x ∈ Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom α ↔
      (∀ a b, a ≠ b →
        SplitTorus.weightCharacter (diagonalTorusWeight r (finProdFinEquiv (a, b))) ≠ α →
          X a b = 0) ∧ (∀ a b, X a a = X b b) := by
  rw [mem_adjointWeightSpace_iff]
  simp only [tangentMatrix_eq_of_tangentEnd_eq _ _ X hX]
  constructor
  · intro h
    constructor
    · intro a b hab hw
      have he := h (finProdFinEquiv (a, b)) (finProdFinEquiv (b, b))
      have hzero : diagonalTorusWeight.{u} r (finProdFinEquiv (b, b)) = 0 := by
        ext i
        simp
      simpa [hzero, conjugationMatrix_apply, Matrix.one_apply, hab] using
        he (by simpa [hzero] using hw)
    · intro a b
      have he := h (finProdFinEquiv (a, b)) (finProdFinEquiv (a, b))
        (by simpa only [sub_self, SplitTorus.weightCharacter_eq_one_iff.mpr rfl] using hα.symm)
      simpa [conjugationMatrix_apply, Matrix.one_apply, sub_eq_zero] using he
  · rintro ⟨hoff, hdiag⟩ a b hw
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective a
    obtain ⟨⟨k, l⟩, rfl⟩ := finProdFinEquiv.surjective b
    by_cases hik : i = k <;> by_cases hlj : l = j
    · subst k; subst l
      simpa [conjugationMatrix_apply] using sub_eq_zero.mpr (hdiag i j)
    · subst k
      have hweight : diagonalTorusWeight.{u} r (finProdFinEquiv (i, j)) -
          diagonalTorusWeight r (finProdFinEquiv (i, l)) =
            diagonalTorusWeight r (finProdFinEquiv (l, j)) := by
        ext q
        simp only [Pi.sub_apply, diagonalTorusWeight_apply, Equiv.symm_apply_apply]
        ring
      simp [conjugationMatrix_apply, Matrix.one_apply, hlj,
        hoff l j hlj (by rwa [hweight] at hw)]
    · subst l
      have hweight : diagonalTorusWeight.{u} r (finProdFinEquiv (i, j)) -
          diagonalTorusWeight r (finProdFinEquiv (k, j)) =
            diagonalTorusWeight r (finProdFinEquiv (i, k)) := by
        ext q
        simp only [Pi.sub_apply, diagonalTorusWeight_apply, Equiv.symm_apply_apply]
        ring
      simp [conjugationMatrix_apply, Matrix.one_apply, hik,
        hoff i k hik (by rwa [hweight] at hw)]
    · simp [conjugationMatrix_apply, hik, hlj]

/-- An elementary projective root vector belongs to its datum's adjoint weight space. -/
theorem rootVector_mem_adjointWeightSpace
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    rootVector (R := R) p ∈ Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) := by
  -- The torus functor stores its character lattice as a categorical object.
  erw [mem_adjointWeightSpace_iff_of_inner (R := R) _ (rootCharacter_ne_one p) _ _
    (tangentEnd_cotangentLinearEquiv_rootVector (R := R) p)]
  constructor
  · intro a b _ hw
    have hp : ¬(p.1.1 = a ∧ p.1.2 = b) := by
      rintro ⟨rfl, rfl⟩
      exact hw (weightCharacter_diagonalTorusWeight p)
    simp [hp]
  · intro a b
    have h (c : Fin (r + 1)) : ¬(p.1.1 = c ∧ p.1.2 = c) := by
      rintro ⟨h₁, h₂⟩
      exact p.2 (h₁.trans h₂.symm)
    simp [h]

private theorem tangentEnd_eq_root_of_mem_adjointWeightSpace
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (x : Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra (r + 1) R)))
    (hx : x ∈ Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p))) :
    ∃ c : R, tangentEnd (R := R) (r + 1) (Derivation.cotangentLinearEquiv (R := R) (B := R) x) =
      LinearMap.mulLeft R (Matrix.single p.1.1 p.1.2 c) -
        LinearMap.mulRight R (Matrix.single p.1.1 p.1.2 c) := by
  obtain ⟨X, hX⟩ := (mem_range_tangentEnd_iff (R := R) (B := R) (r + 1) _).mp ⟨_, rfl⟩
  obtain ⟨hoff, hdiag⟩ := (mem_adjointWeightSpace_iff_of_inner _
    (rootCharacter_ne_one p) x X hX).mp hx
  have hnormal : X = Matrix.single p.1.1 p.1.2 (X p.1.1 p.1.2) +
      X (Fin.last r) (Fin.last r) • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) R) := by
    ext a b
    by_cases hab : a = b
    · subst b
      have hp : ¬(p.1.1 = a ∧ p.1.2 = a) := by
        rintro ⟨h₁, h₂⟩
        exact p.2 (h₁.trans h₂.symm)
      simp [hp, hdiag a (Fin.last r)]
    · by_cases hp : p.1.1 = a ∧ p.1.2 = b
      · obtain ⟨rfl, rfl⟩ := hp
        simp [hab]
      · have he := hoff a b hab (by
          intro h
          have hpair := (weightCharacter_diagonalTorusWeight_eq_root_iff p a b).mp h
          exact hp ⟨hpair.1.symm, hpair.2.symm⟩)
        simp [hp, hab, he]
  refine ⟨X p.1.1 p.1.2, ?_⟩
  rw [hX]
  conv_lhs => rw [hnormal]
  ext Y a b
  simp only [LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.add_apply]
  abel

/-- Each projective adjoint root space is exactly the line supplied by its elementary
root subgroup. -/
theorem adjointWeightSpace_root_eq_span
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
        (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) =
      R ∙ rootVector (R := R) p := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc⟩ := tangentEnd_eq_root_of_mem_adjointWeightSpace p x hx
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    apply (Derivation.cotangentLinearEquiv (R := R)
      (A := coordinateHopfAlgebra (r + 1) R) (B := R)).injective
    apply tangentEnd_injective (r + 1)
    rw [map_smul, map_smul, tangentEnd_cotangentLinearEquiv_rootVector, hc]
    have hs : Matrix.single p.1.1 p.1.2 c = c • Matrix.single p.1.1 p.1.2 (1 : R) := by
      simp
    rw [hs]
    apply LinearMap.ext
    intro Y
    simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact rootVector_mem_adjointWeightSpace p

/-- Every projective adjoint root space is free of rank one with its elementary
root parametrization as generator. -/
def rootSpaceEquiv (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    R ≃ₗ[R] Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) :=
  (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R _ (rootVector (R := R) p))
    (rootVector_smul_left_injective p)).trans
      (LinearEquiv.ofEq _ _ (by
        rw [LinearMap.range_toSpanSingleton, adjointWeightSpace_root_eq_span]))

/-- The root-space parametrization sends `c` to `c` times the normalized vector. -/
@[simp]
theorem rootSpaceEquiv_apply_coe
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) (c : R) :
    (rootSpaceEquiv (R := R) p c :
      Module.Dual R (Bialgebra.CotangentSpace R (coordinateHopfAlgebra (r + 1) R))) =
      c • rootVector (R := R) p := by
  rw [rootSpaceEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  exact LinearEquiv.ofInjective_apply _ _

/-- The inverse root-space coordinate is the distinguished entry of its action on `E_jj`. -/
@[simp]
theorem rootSpaceEquiv_symm_apply
    (p : SplitTorus.CoordinateRootIndex (Fin (r + 1)))
    (x : Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r R).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p))) :
    (rootSpaceEquiv (R := R) p).symm x =
      tangentEnd (R := R) (r + 1) (Derivation.cotangentLinearEquiv (R := R) (B := R) x.1)
        (Matrix.single p.1.2 p.1.2 1) p.1.1 p.1.2 := by
  have h := congrArg Subtype.val ((rootSpaceEquiv (R := R) p).apply_symm_apply x)
  rw [rootSpaceEquiv_apply_coe] at h
  have he := congrArg (fun y ↦
    tangentEnd (R := R) (r + 1) (Derivation.cotangentLinearEquiv (R := R) (B := R) y)
      (Matrix.single p.1.2 p.1.2 1) p.1.1 p.1.2) h
  rw [tangentEnd_smul_rootVector_apply] at he
  exact he

/-- The nontrivial adjoint weights of `PGL` are exactly the roots of its normalized
diagonal root datum. The converse excludes every other character. -/
theorem mem_nontrivialAdjointWeights_iff_exists_diagonalRoot [Nontrivial R]
    (α : Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) :
    α ∈ Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom ↔
      ∃ p : SplitTorus.CoordinateRootIndex (Fin (r + 1)),
        α = Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p) := by
  constructor
  · rw [Derivation.mem_nontrivialAdjointWeights]
    rintro ⟨hα, hspace⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hspace
    obtain ⟨X, hX⟩ := (mem_range_tangentEnd_iff (R := R) (B := R) (r + 1) _).mp ⟨_, rfl⟩
    obtain ⟨hoff, hdiag⟩ := (mem_adjointWeightSpace_iff_of_inner α hα x X hX).mp hx
    by_contra hroots
    have hzero (a b : Fin (r + 1)) (hab : a ≠ b) : X a b = 0 := by
      apply hoff a b hab
      rw [weightCharacter_diagonalTorusWeight ⟨(a, b), hab⟩]
      exact fun h ↦ hroots ⟨⟨(a, b), hab⟩, h.symm⟩
    have hscalar : X = X (Fin.last r) (Fin.last r) • 1 := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [hdiag a (Fin.last r)]
      · simp [hzero a b hab, hab]
    apply hx0
    apply (Derivation.cotangentLinearEquiv (R := R)
      (A := coordinateHopfAlgebra (r + 1) R) (B := R)).injective
    apply tangentEnd_injective (r + 1)
    rw [map_zero, map_zero, hX, hscalar]
    apply LinearMap.ext
    intro Y
    simp
  · rintro ⟨p, rfl⟩
    rw [Derivation.mem_nontrivialAdjointWeights]
    refine ⟨rootCharacter_ne_one p, ?_⟩
    intro hspace
    have hx := rootVector_mem_adjointWeightSpace (R := R) p
    -- Match the categorical character lattice in the membership statement.
    erw [hspace, Submodule.mem_bot] at hx
    exact rootVector_ne_zero p hx

/-- The packaged roots equal the entire set of nontrivial adjoint weights. -/
theorem range_ofAdd_diagonalRootDatum_root_eq_nontrivialAdjointWeights [Nontrivial R] :
    Set.range (fun p : SplitTorus.CoordinateRootIndex (Fin (r + 1)) ↦
        Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p)) =
      Derivation.nontrivialAdjointWeights (diagonalTorusCoordinateMap r R).hom := by
  ext α
  rw [Set.mem_range, mem_nontrivialAdjointWeights_iff_exists_diagonalRoot]
  exact exists_congr fun p ↦ eq_comm

/-- Every projective adjoint root space over a field is one-dimensional, including
when the characteristic divides the matrix size. -/
theorem finrank_adjointWeightSpace_root_eq_one
    {k : Type u} [Field k] (p : SplitTorus.CoordinateRootIndex (Fin (r + 1))) :
    Module.finrank k (Derivation.adjointWeightSpace (diagonalTorusCoordinateMap r k).hom
      (Multiplicative.ofAdd ((diagonalRootDatum.{u} r).root p))) = 1 := by
  rw [← (rootSpaceEquiv (R := k) p).finrank_eq]
  exact Module.finrank_self k

end

end TauCeti.ProjectiveGeneralLinear
