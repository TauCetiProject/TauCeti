/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Grassmannian.Chart.Transition
public import TauCeti.RingTheory.Grassmannian.HopfIdeal

/-!
# Affine charts parametrising Hopf ideals

For a commutative Hopf algebra `H` over `R` and a tuple `x : Fin k → H`, the quotient
`HopfIdealChart.CoordinateRing R x` of the Grassmannian chart algebra represents the Hopf ideals
in `A ⊗[R] H` whose quotients have the images of `1 ⊗ x i` as a basis. Its universal
quotient is a commutative Hopf algebra, free of rank `k` over the chart algebra. Thus its
spectrum is the universal finite free subgroup on this chart of the subgroup parameter space.

The construction uses `Module.Grassmannian.chartHomEquiv` for the ambient chart and
`Module.Grassmannian.hopfIdealLocus` for the closed equations. The equations agree under
the Grassmannian transition isomorphisms, as needed to glue the closed charts.

## References

* The Stacks Project, Tag 089R, for the Grassmannian functor.
-/

public noncomputable section

open Module.Grassmannian TensorProduct

universe u

namespace TauCeti.HopfIdealChart

variable (R : Type u) [CommRing R] {H : Type u} [CommRing H] [HopfAlgebra R H]
  {k : ℕ} (x : Fin k → H)

/-- The equations cutting out Hopf ideals in the Grassmannian chart at `x`. -/
def ideal : Ideal (ChartAlgebra R x) :=
  ((chartHomEquiv R x _ (AlgHom.id R _)).1).hopfIdealLocus

-- A nominal type keeps instance search from choosing the module structure from the inner
-- quotient defining `ChartAlgebra` when forming tensor products over `R`.
/-- The coordinate algebra of the closed chart parametrising rank-`k` Hopf quotients
with basis given by the images of `x`. -/
def CoordinateRing := ChartAlgebra R x ⧸ ideal R x
  deriving CommRing, Algebra R

/-- The closed immersion of charts is induced by this quotient homomorphism. -/
def mk : ChartAlgebra R x →ₐ[R] CoordinateRing R x :=
  Ideal.Quotient.mkₐ R (ideal R x)

/-- The closed chart is a quotient of the ambient affine chart. -/
theorem mk_surjective : Function.Surjective (mk R x) :=
  Ideal.Quotient.mk_surjective

/-- The kernel of the chart quotient map is precisely the Hopf-ideal equations. -/
@[simp]
theorem ker_mk : RingHom.ker (mk R x) = ideal R x :=
  Ideal.Quotient.mkₐ_ker R _

variable {R x}

/-- Factor a homomorphism satisfying the Hopf equations through the closed chart. -/
def lift {A : Type u} [CommRing A] [Algebra R A] (f : ChartAlgebra R x →ₐ[R] A)
    (hf : ideal R x ≤ RingHom.ker f) : CoordinateRing R x →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ f fun _ ha ↦ RingHom.mem_ker.mp (hf ha)

/-- Factoring through the closed chart does not change the ambient chart homomorphism. -/
@[simp]
theorem lift_comp_mk {A : Type u} [CommRing A] [Algebra R A]
    (f : ChartAlgebra R x →ₐ[R] A) (hf : ideal R x ≤ RingHom.ker f) :
    (lift f hf).comp (mk R x) = f :=
  Ideal.Quotient.liftₐ_comp _ _ _

/-- A map from the ambient chart satisfies its Hopf equations precisely when its
classified submodule is a Hopf ideal. -/
theorem ideal_le_ker_iff {A : Type u} [CommRing A] [Algebra R A]
    (f : ChartAlgebra R x →ₐ[R] A) :
    ideal R x ≤ RingHom.ker f ↔
      ∃ I : Ideal (A ⊗[R] H),
        I.restrictScalars A = (chartHomEquiv R x A f).1.toSubmodule ∧ I.IsHopfIdeal A := by
  rw [ideal, hopfIdealLocus_le_ker_iff]
  have h := chartHomEquiv_comp x f (AlgHom.id R _)
  rw [AlgHom.comp_id] at h
  rw [← h]
  constructor
  · rintro ⟨I, hI, -, hHopf⟩
    exact ⟨I, hI, hHopf⟩
  · rintro ⟨I, hI, hHopf⟩
    exact ⟨I, hI, inferInstance, hHopf⟩

/-- The Hopf equations evaluated at a chart point are the image of the universal equations. -/
@[simp]
theorem ideal_map {A : Type u} [CommRing A] [Algebra R A] (f : ChartAlgebra R x →ₐ[R] A) :
    Ideal.map f (ideal R x) = (chartHomEquiv R x A f).1.hopfIdealLocus := by
  have h := chartHomEquiv_comp x f (AlgHom.id R _)
  rw [AlgHom.comp_id] at h
  rw [h, hopfIdealLocus_map]
  rfl

variable (R x)

/-- The Grassmannian point on the closed chart, whose quotient is the universal Hopf quotient. -/
def universalPoint : chart (CoordinateRing R x) (fun i ↦ (1 : CoordinateRing R x) ⊗ₜ[R] x i) :=
  chartHomEquiv R x _ (mk R x)

/-- The submodule at the universal point is a Hopf ideal. -/
private theorem exists_universalIdeal :
    ∃ I : Ideal (CoordinateRing R x ⊗[R] H),
      I.restrictScalars (CoordinateRing R x) = (universalPoint R x).1.toSubmodule ∧
        I.IsHopfIdeal (CoordinateRing R x) :=
  (ideal_le_ker_iff (mk R x)).mp (by rw [ker_mk])

/-- The universal Hopf ideal in the base change of `H` to the closed chart. -/
def universalIdeal : Ideal (CoordinateRing R x ⊗[R] H) :=
  (exists_universalIdeal R x).choose

/-- The universal ideal has the underlying submodule classified by the universal point. -/
@[simp]
theorem universalIdeal_restrictScalars :
    (universalIdeal R x).restrictScalars (CoordinateRing R x) =
      (universalPoint R x).1.toSubmodule :=
  (exists_universalIdeal R x).choose_spec.1

instance : (universalIdeal R x).IsHopfIdeal (CoordinateRing R x) :=
  (exists_universalIdeal R x).choose_spec.2

/-- The universal finite free Hopf quotient on the chart. -/
abbrev Quotient := (CoordinateRing R x ⊗[R] H) ⧸ universalIdeal R x

/-- The images of `1 ⊗ x i` identify the universal quotient with a free module of rank `k`. -/
def quotientEquiv : (Fin k → CoordinateRing R x) ≃ₗ[CoordinateRing R x] Quotient R x :=
  (chartQuotEquiv (universalPoint R x)).trans
    (Submodule.quotEquivOfEq (universalPoint R x).1.toSubmodule
      ((universalIdeal R x).restrictScalars (CoordinateRing R x))
      (universalIdeal_restrictScalars R x).symm)

/-- The quotient equivalence sends coordinates to the class of their linear combination. -/
@[simp]
theorem quotientEquiv_apply (v : Fin k → CoordinateRing R x) :
    quotientEquiv R x v = Ideal.Quotient.mk (universalIdeal R x)
      (Fintype.linearCombination (CoordinateRing R x)
        (fun i ↦ (1 : CoordinateRing R x) ⊗ₜ[R] x i) v) := by
  unfold quotientEquiv
  -- The ideal quotient and its restricted submodule have derived scalar actions.
  erw [LinearEquiv.trans_apply, chartQuotEquiv_apply, Submodule.quotEquivOfEq_mk]

/-- The inverse quotient equivalence sends distinguished generators to coordinate vectors. -/
@[simp]
theorem quotientEquiv_symm_apply_mk (i : Fin k) :
    (quotientEquiv R x).symm
      (Ideal.Quotient.mk (universalIdeal R x) ((1 : CoordinateRing R x) ⊗ₜ[R] x i)) =
        Pi.single i 1 := by
  apply (LinearEquiv.symm_apply_eq _).2
  rw [quotientEquiv_apply, Fintype.linearCombination_apply_single, one_smul]

/-- The universal quotient has its distinguished basis, induced by the tuple `x`. -/
def basis : Module.Basis (Fin k) (CoordinateRing R x) (Quotient R x) :=
  (Pi.basisFun (CoordinateRing R x) (Fin k)).map (quotientEquiv R x)

/-- The distinguished basis vectors are the images of the chosen elements of `H`. -/
@[simp]
theorem basis_apply (i : Fin k) :
    basis R x i = Ideal.Quotient.mk (universalIdeal R x) ((1 : CoordinateRing R x) ⊗ₜ[R] x i) := by
  unfold basis quotientEquiv
  rw [Module.Basis.map_apply, Pi.basisFun_apply]
  -- Rewriting through the ideal quotient and its restricted submodule needs the
  -- derived scalar actions to be unfolded.
  erw [LinearEquiv.trans_apply, chartQuotEquiv_apply,
    Fintype.linearCombination_apply_single, one_smul, Submodule.quotEquivOfEq_mk]

instance : Module.Free (CoordinateRing R x) (Quotient R x) :=
  Module.Free.of_basis (basis R x)

instance : Module.Finite (CoordinateRing R x) (Quotient R x) :=
  Module.Finite.of_basis (basis R x)

variable {R x}

/-- The closed chart represents the Hopf-ideal subfunctor of the ambient Grassmannian chart. -/
def homEquiv (A : Type u) [CommRing A] [Algebra R A] :
    (CoordinateRing R x →ₐ[R] A) ≃
      {N : chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) //
        ∃ I : Ideal (A ⊗[R] H), I.restrictScalars A = N.1.toSubmodule ∧ I.IsHopfIdeal A} where
  toFun f := ⟨chartHomEquiv R x A (f.comp (mk R x)),
    (ideal_le_ker_iff _).mp fun a ha ↦ by
      have hz : mk R x a = 0 := RingHom.mem_ker.mp (by rwa [ker_mk])
      exact (congrArg f hz).trans (map_zero f)⟩
  invFun N := lift ((chartHomEquiv R x A).symm N.1)
    ((ideal_le_ker_iff _).mpr (by simpa using N.2))
  left_inv f := by
    apply Ideal.Quotient.algHom_ext R
    exact (lift_comp_mk _ _).trans (Equiv.symm_apply_apply _ _)
  right_inv N := Subtype.ext <| by
    dsimp only
    rw [lift_comp_mk, Equiv.apply_symm_apply]

/-- Forgetting the Hopf condition in `homEquiv` gives the ambient chart point. -/
@[simp]
theorem homEquiv_apply {A : Type u} [CommRing A] [Algebra R A] (f : CoordinateRing R x →ₐ[R] A) :
    (homEquiv A f).1 = chartHomEquiv R x A (f.comp (mk R x)) :=
  (rfl)

/-- The inverse universal correspondence evaluates the ambient chart coordinates at the
linear quotient map attached to the given Hopf ideal. -/
@[simp]
theorem homEquiv_symm_apply_mk {A : Type u} [CommRing A] [Algebra R A]
    (N : {N : chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) //
      ∃ I : Ideal (A ⊗[R] H), I.restrictScalars A = N.1.toSubmodule ∧ I.IsHopfIdeal A})
    (a : ChartAlgebra R x) :
    (homEquiv A).symm N (mk R x a) =
      (chartHomEquiv R x A).symm N.1 a :=
  (rfl)

/-- The universal correspondence commutes with arbitrary changes of the test algebra. -/
theorem homEquiv_comp {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (g : CoordinateRing R x →ₐ[R] A) :
    (homEquiv B (f.comp g)).1.1 = map f (homEquiv A g).1.1 := by
  simp only [homEquiv_apply, AlgHom.comp_assoc, chartHomEquiv_comp]

/-- The Hopf-ideal equations agree on overlaps under the ambient Grassmannian transitions.
Consequently the closed chart loci have the same restrictions to either overlap. -/
theorem map_ideal_transition (y : Fin k → H) :
    Ideal.map (transitionAlgEquiv R x y).toAlgHom
        (Ideal.map (IsScalarTower.toAlgHom R (ChartAlgebra R y) (OverlapAlgebra R y x))
          (ideal R y)) =
      Ideal.map (IsScalarTower.toAlgHom R (ChartAlgebra R x) (OverlapAlgebra R x y))
        (ideal R x) := by
  have h := overlapHomEquiv_comp_transitionAlgEquiv x y (AlgHom.id R _)
  simp only [coe_overlapHomEquiv_apply, AlgHom.id_comp] at h
  have heq := congrArg (fun N ↦ N.hopfIdealLocus) h
  erw [Ideal.map_map]
  simp only [← ideal_map] at heq
  exact heq

end TauCeti.HopfIdealChart
