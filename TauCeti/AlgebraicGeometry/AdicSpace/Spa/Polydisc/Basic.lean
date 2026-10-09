/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import TauCeti.RingTheory.Huber.WeightedEval.Continuous
public import TauCeti.RingTheory.Huber.WeightedEval.Hom

import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Complete
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# The closed polydisc, its classical points and its translations

The *closed polydisc* of dimension `k` over a nonarchimedean ring `A` is the adic spectrum
`Spa (A⟨T₁, …, Tₖ⟩, A⟨T₁, …, Tₖ⟩°)` of the restricted power series ring with its power-bounded
subring as plus ring. For a complete nonarchimedean field this is the closed unit polydisc of rigid
geometry, the affinoid whose points Wedhorn classifies in Example 7.57; the rings of Definition
7.56 are its quotients.

Its first points are the *classical* ones, the "end points" of Wedhorn's picture. A point `x` of
`Spa (A, A°)` and a tuple `a ∈ (A°)ᵏ` give the point `f ↦ x (f (a))`: evaluation at `a` is a
continuous ring homomorphism `A⟨T⟩ → A` (Wedhorn, Proposition 5.50), it carries `A⟨T⟩°` into `A°`
because it retracts the continuous constant embedding `weightedC` — continuous ring homomorphisms
do not preserve power-boundedness in general — and the point is the pullback of `x` along it. When
`x` has trivial support, for instance whenever `A` is a field, distinct tuples give distinct
points.

The evaluation is taken along the identity of `A`, so `A` carries the hypotheses under which
Wedhorn's evaluation converges: complete, Hausdorff, and nonarchimedean as a uniform additive
group. For the polydisc itself, a nonarchimedean ring topology suffices.

Under the same hypotheses, evaluating along the constant embedding `A → A⟨T⟩` at the shifted
variables `Tᵢ + aᵢ` translates the polydisc: `f(T) ↦ f(T + a)` is a continuous ring endomorphism
of `A⟨T⟩`, translations compose additively, and so each one is invertible and preserves `A⟨T⟩°`.
Pulling a point back along a translation recentres it, which is how the Gauss points of discs about
arbitrary centres are obtained from those about the origin.

## Main definitions

* `TauCeti.ValuationSpectrum.closedPolydisc`: the closed polydisc `Spa (A⟨T⟩, A⟨T⟩°)`, with
  `mem_closedPolydisc_iff` as its membership rule.
* `TauCeti.ValuationSpectrum.evalAtHom`: evaluation of restricted power series at `a ∈ (A°)ᵏ`, as a
  ring homomorphism `A⟨T⟩ →+* A`.
* `TauCeti.ValuationSpectrum.classicalPoint`: the classical point of the closed polydisc attached
  to a point of `Spa (A, A°)` and a tuple `a ∈ (A°)ᵏ`.
* `TauCeti.ValuationSpectrum.translateHom`: the translation `Tᵢ ↦ Tᵢ + aᵢ` of `A⟨T⟩` by
  `a ∈ (A°)ᵏ`.

## Main results

* `TauCeti.ValuationSpectrum.continuous_evalAtHom` and
  `TauCeti.ValuationSpectrum.evalAtHom_mem_powerBoundedSubring`: evaluation at `a` is a morphism
  of Huber pairs `(A⟨T⟩, A⟨T⟩°) → (A, A°)`.
* `TauCeti.ValuationSpectrum.classicalPoint_vle`: the classical point compares `f` and `g` as `x`
  compares `f (a)` and `g (a)`.
* `TauCeti.ValuationSpectrum.classicalPoint_injective`: when `x` has trivial support, the
  classical points are parametrised faithfully by `(A°)ᵏ`;
  `TauCeti.ValuationSpectrum.classicalPoint_injective_of_isField` is the case of a field.
* `TauCeti.ValuationSpectrum.hasSum_translateHom`: `f(T + a)` is the sum of the translated
  monomials of `f`.
* `TauCeti.ValuationSpectrum.translateHom_comp_translateHom`: translating by `b` and then by `a`
  is translating by `a + b`.
* `TauCeti.ValuationSpectrum.translateHom_mem_powerBoundedSubring`: translation preserves
  `A⟨T⟩°`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.50, Definition 7.56
  and Example 7.57.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section Polydisc

variable (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **The closed polydisc of dimension `k` over `A`**: the adic spectrum of the restricted power
series ring `A⟨T₁, …, Tₖ⟩` with its power-bounded subring as plus ring. Over a complete
nonarchimedean field this is the closed unit polydisc (Wedhorn, Example 7.57 at `k = 1`). -/
def closedPolydisc :
    Set (Spv (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)) :=
  spa (powerBoundedSubring _)

/-- The set-level characterization of the closed polydisc. `closedPolydisc` is not `@[expose]`d,
so its body is invisible across the module boundary and this equation is how consumers apply
set-level results to it — the same role `spa_def` plays for `spa`, which is likewise unexposed. -/
lemma closedPolydisc_def :
    closedPolydisc k A =
      spa (powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight)) :=
  (rfl)

/-- Membership in the closed polydisc: a point of `Spv (A⟨T₁, …, Tₖ⟩)` lies on the polydisc
exactly when it is continuous and sub-unit on the power-bounded elements. This is `mem_spa_iff`
specialized to the polydisc, and is the elimination rule consumers use on a point of it. -/
@[simp]
lemma mem_closedPolydisc_iff
    (v : Spv (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
      isWeightFamily_one_weight)) :
    v ∈ closedPolydisc k A ↔ v.IsContinuous ∧
      ∀ f ∈ powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight), v.toValuativeRel.vle f 1 := by
  rw [closedPolydisc_def, mem_spa_iff]

end Polydisc

section ClassicalPoints

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T3Space A]

/-- **Evaluation at `a ∈ (A°)ᵏ`** as a ring homomorphism `A⟨T₁, …, Tₖ⟩ →+* A`: Wedhorn's
evaluation of restricted power series along the identity of `A`, which converges because the
coordinates of `a` are power-bounded. -/
noncomputable def evalAtHom (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+* A :=
  weightedEvalHom isWeightFamily_one_weight continuousAt_id
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded (RingHom.id A) a).2 ha)

/-- Evaluation at `a` is continuous. -/
theorem continuous_evalAtHom (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) :
    Continuous (evalAtHom a ha) :=
  continuous_weightedEvalHom _ _ _

/-- Evaluation at `a` sends the variable `Tᵢ` to `aᵢ`. -/
@[simp]
theorem evalAtHom_weightedX (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) (i : Fin k) :
    evalAtHom a ha (weightedX _ isWeightFamily_one_weight i) = a i :=
  weightedEvalHom_weightedX _ _ _ i

/-- Evaluation at `a` fixes the constants. -/
@[simp]
theorem evalAtHom_weightedC (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) (c : A) :
    evalAtHom a ha (weightedC _ isWeightFamily_one_weight c) = c :=
  weightedEvalHom_weightedC _ _ _ c

/-- Evaluation at `a` carries `A⟨T⟩°` into `A°`. Together with `continuous_evalAtHom` this makes
evaluation a morphism of Huber pairs `(A⟨T⟩, A⟨T⟩°) → (A, A°)`. -/
theorem evalAtHom_mem_powerBoundedSubring (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hf : f ∈ powerBoundedSubring _) : evalAtHom a ha f ∈ powerBoundedSubring A := by
  -- A continuous ring homomorphism need not preserve power-boundedness; this one does because it
  -- retracts `weightedC`, so `IsPowerBounded.map`'s surjectivity-onto-neighbourhoods side condition
  -- holds: every neighbourhood `V` of zero in `A` is hit from the neighbourhood `C⁻¹ V` upstairs.
  refine mem_powerBoundedSubring.mpr
    ((mem_powerBoundedSubring.mp hf).map (continuous_evalAtHom a ha).continuousAt fun V hV ↦ ?_)
  -- `C⁻¹ V` is a neighbourhood of zero and evaluation maps `C c` back to `c`.
  refine Filter.mem_of_superset
    ((continuous_weightedC isWeightFamily_one_weight).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])) fun c hc ↦ ?_
  exact ⟨_, hc, evalAtHom_weightedC a ha c⟩

/-- **The classical point of the closed polydisc** attached to a point `x` of `Spa (A, A°)` and a
tuple `a ∈ (A°)ᵏ`: the pullback of `x` along evaluation at `a`, the valuation `f ↦ x (f (a))`. -/
noncomputable def classicalPoint (x : spa (powerBoundedSubring A)) (a : Fin k → A)
    (ha : ∀ i, IsPowerBounded (a i)) : closedPolydisc k A :=
  spaComap (evalAtHom a ha) (continuous_evalAtHom a ha) _ _
    (fun _ hf ↦ evalAtHom_mem_powerBoundedSubring a ha hf) x

/-- The classical point at `a` compares `f` and `g` as `x` compares their values at `a`: the
elimination rule that rewrites a comparison at a classical point into one after `evalAtHom`. -/
@[simp]
theorem classicalPoint_vle (x : spa (powerBoundedSubring A)) (a : Fin k → A)
    (ha : ∀ i, IsPowerBounded (a i))
    (f g : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    (classicalPoint x a ha).1.toValuativeRel.vle f g ↔
      x.1.toValuativeRel.vle (evalAtHom a ha f) (evalAtHom a ha g) := by
  rw [classicalPoint, spaComap_val, comap_vle]

/-- **Distinct tuples give distinct classical points** when `x` has trivial support. The
hypothesis is `ValuativeRel.supp = ⊥` for `x`, written out: the valuative relation here is the
term `x.1.toValuativeRel`, not an instance, so `ValuativeRel.supp` is not directly available. -/
theorem classicalPoint_injective (x : spa (powerBoundedSubring A))
    (hx : ∀ c : A, x.1.toValuativeRel.vle c 0 → c = 0) :
    Function.Injective fun a : {a : Fin k → A // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2 := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ h
  -- The witness separating the tuples is `Tᵢ - bᵢ`: it evaluates to `0` at `b`, and to `aᵢ - bᵢ`
  -- at `a`, so equality of the two points forces `aᵢ - bᵢ` into the support.
  refine Subtype.ext (funext fun i ↦ sub_eq_zero.mp (hx _ ?_))
  have h' := congrArg (fun y : closedPolydisc k A ↦ y.1.toValuativeRel.vle
    (weightedX _ isWeightFamily_one_weight i - weightedC _ isWeightFamily_one_weight (b i)) 0) h
  simp only [classicalPoint_vle, map_sub, map_zero, evalAtHom_weightedX, evalAtHom_weightedC,
    sub_self] at h'
  exact h'.mpr (x.1.toValuativeRel.vle_refl 0)

/-- Over a field every point of `Spa (A, A°)` has trivial support, so the classical points are
parametrised faithfully by `(A°)ᵏ`. -/
theorem classicalPoint_injective_of_isField (hA : IsField A) (x : spa (powerBoundedSubring A)) :
    Function.Injective fun a : {a : Fin k → A // ∀ i, IsPowerBounded (a i)} ↦
      classicalPoint x a.1 a.2 :=
  classicalPoint_injective x fun c hc ↦ by
    -- Mathlib's `ValuativeRel.vle_zero_iff` says exactly this over a division ring, but wants
    -- `[DivisionRing K]` and the relation as an instance. Installing `hA.toField` routes
    -- `Semiring A` through `Field.toSemifield.toDivisionSemiring.toSemiring`, defeq to but not
    -- syntactically `CommRing.toCommSemiring.toSemiring`, so `x.1.toValuativeRel` stops
    -- typechecking against it. Inverting `c` is shorter than transporting across that diamond.
    by_contra hne
    obtain ⟨d, hd⟩ := hA.mul_inv_cancel hne
    have h := x.1.toValuativeRel.mul_vle_mul_left hc d
    rw [hd, zero_mul] at h
    exact x.1.toValuativeRel.not_vle_one_zero h

end ClassicalPoints

section Translation

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T3Space A]

omit [IsUniformAddGroup A] [CompleteSpace A] [T3Space A] in
/-- The shifted variables `Tᵢ + aᵢ` are power-bounded in `A⟨T₁, …, Tₖ⟩` when the `aᵢ` are
power-bounded in `A`. -/
private theorem isPowerBounded_weightedX_add_weightedC (a : Fin k → A)
    (ha : ∀ i, IsPowerBounded (a i)) (i : Fin k) :
    IsPowerBounded (weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i +
      weightedC _ isWeightFamily_one_weight (a i)) :=
  (isPowerBounded_weightedX_one_weight i).add (isPowerBounded_weightedC _ (ha i))

/-- **Translation by `a ∈ (A°)ᵏ`**: the substitution `Tᵢ ↦ Tᵢ + aᵢ`, as a ring endomorphism of
`A⟨T₁, …, Tₖ⟩`. It is Wedhorn's evaluation of restricted power series along the constant
embedding `A → A⟨T⟩`, at the power-bounded tuple `(Tᵢ + aᵢ)ᵢ`. -/
noncomputable def translateHom (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) :
    weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight →+*
      weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight :=
  weightedEvalHom isWeightFamily_one_weight
    (continuous_weightedC isWeightFamily_one_weight).continuousAt
    ((isWeightBounded_one_weight_iff_forall_isPowerBounded _ _).mpr
      (isPowerBounded_weightedX_add_weightedC a ha))

/-- **The translate of `f` is the sum of its translated monomials**: `f(T + a)` is the sum of the
terms `aν (T + a)ν`, where `aν` is the coefficient of `Tν` in `f`. -/
theorem hasSum_translateHom (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    HasSum (fun ν : Fin k →₀ ℕ ↦
        weightedC _ isWeightFamily_one_weight
            (MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A)) *
          ∏ i, (weightedX _ isWeightFamily_one_weight i +
            weightedC _ isWeightFamily_one_weight (a i)) ^ ν i)
      (translateHom a ha f) := by
  rw [translateHom, coe_weightedEvalHom]
  convert hasSum_weightedEval_of_forall_isPowerBounded
    (continuous_weightedC isWeightFamily_one_weight).continuousAt
    (isPowerBounded_weightedX_add_weightedC a ha) (mem_weightedRestrictedSubring.mp f.2) using 1
  exact funext fun ν ↦ (weightedEvalTerm_def _ _ _ ν).symm

/-- Translation is continuous. -/
theorem continuous_translateHom (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) :
    Continuous (translateHom a ha) := by
  rw [translateHom]
  exact continuous_weightedEvalHom _ _ _

/-- Translation fixes the constants. -/
@[simp]
theorem translateHom_weightedC (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) (c : A) :
    translateHom a ha (weightedC _ isWeightFamily_one_weight c) =
      weightedC _ isWeightFamily_one_weight c := by
  rw [translateHom, weightedEvalHom_weightedC]

/-- Translation by `a` sends the variable `Tᵢ` to `Tᵢ + aᵢ`. -/
@[simp]
theorem translateHom_weightedX (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) (i : Fin k) :
    translateHom a ha (weightedX _ isWeightFamily_one_weight i) =
      weightedX _ isWeightFamily_one_weight i + weightedC _ isWeightFamily_one_weight (a i) := by
  rw [translateHom, weightedEvalHom_weightedX]

/-- Translation by zero is the identity. -/
@[simp]
theorem translateHom_zero :
    translateHom (0 : Fin k → A) (fun _ ↦ isPowerBounded_zero) =
      RingHom.id (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight) :=
  weightedRestrictedSubring_ringHom_ext_of_continuous _ (continuous_translateHom _ _)
    continuous_id (by simp) (by simp)

/-- **Translations compose additively**: translating by `b` and then by `a` is translating by
`a + b`. -/
theorem translateHom_comp_translateHom (a b : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (hb : ∀ i, IsPowerBounded (b i)) :
    (translateHom a ha).comp (translateHom b hb) =
      translateHom (a + b) (fun i ↦ (ha i).add (hb i)) :=
  weightedRestrictedSubring_ringHom_ext_of_continuous _
    ((continuous_translateHom a ha).comp (continuous_translateHom b hb))
    (continuous_translateHom _ _) (by simp) (by simp [add_assoc])

/-- **Translations compose additively**, applied to a series. -/
@[simp]
theorem translateHom_translateHom (a b : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (hb : ∀ i, IsPowerBounded (b i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    translateHom a ha (translateHom b hb f) = translateHom (a + b) (fun i ↦ (ha i).add (hb i)) f :=
  RingHom.congr_fun (translateHom_comp_translateHom a b ha hb) f

/-- Translation by `-a` undoes translation by `a`. -/
theorem translateHom_neg_translateHom (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight) :
    translateHom (-a) (fun i ↦ (ha i).neg) (translateHom a ha f) = f := by
  simp

/-- Translation is injective. -/
theorem translateHom_injective (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i)) :
    Function.Injective (translateHom a ha) :=
  Function.LeftInverse.injective (translateHom_neg_translateHom a ha)

/-- Translation carries `A⟨T⟩°` into itself, so it is an endomorphism of the Huber pair
`(A⟨T⟩, A⟨T⟩°)` and `spaComap` along it maps the closed polydisc to itself. -/
theorem translateHom_mem_powerBoundedSubring (a : Fin k → A) (ha : ∀ i, IsPowerBounded (a i))
    {f : weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight}
    (hf : f ∈ powerBoundedSubring _) : translateHom a ha f ∈ powerBoundedSubring _ := by
  -- A continuous ring homomorphism need not preserve power-boundedness; translation does because
  -- translation by `-a` inverts it, so the image of a neighbourhood `V` of zero contains the
  -- neighbourhood of zero obtained by pulling `V` back along that inverse.
  refine mem_powerBoundedSubring.mpr
    ((mem_powerBoundedSubring.mp hf).map (continuous_translateHom a ha).continuousAt fun V hV ↦ ?_)
  refine Filter.mem_of_superset
    ((continuous_translateHom (-a) fun i ↦ (ha i).neg).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])) fun g hg ↦ ⟨_, hg, by simp⟩

end Translation

end TauCeti.ValuationSpectrum
