/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.KnotTheory.Grid.Grading.SimplyBlocked

/-!
# The Maslov-graded unblocked grid complex

At each Alexander degree `a`, the homogeneous pieces of `GC⁻` form a chain complex
indexed by Maslov degree. Its homology in degree `m` is the `(m, a)`-graded unblocked
grid homology. The differential is the restriction of the total rectangle-counting
differential; its square vanishes over any commutative ring of characteristic two.

Multiplication by a variable embeds each homogeneous chain module into the module
of bidegree two lower in Maslov and one lower in Alexander. Specialization at one
variable equal to zero gives a chain map to the graded simply blocked complex,
surjective in every Maslov degree. In each bidegree its kernel is exactly the
image of the variable map, giving the degreewise short exact sequence with both
grading shifts explicit.

These complexes retain both gradings when studying grid moves or comparing the
unblocked and simply blocked theories. Homology and induced maps use
Mathlib's homological-complex API.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.3 and 4.6.
-/

public section

open CategoryTheory MvPolynomial

namespace TauCeti.OddComponentGridDiagram

variable {n : ℕ} (G : OddComponentGridDiagram n)

/-- The unblocked differential between consecutive Maslov degrees at Alexander degree `a`. -/
noncomputable def gradedUnblockedDifferential (R : Type*) [CommSemiring R] (a m : ℤ) :
    G.bigradedChainMinusPiece R (m + 1, a) →ₗ[R] G.bigradedChainMinusPiece R (m, a) :=
  ((G.1.unblockedDifferential R).restrictScalars R).restrict fun c hc => by
    simpa using G.unblockedDifferential_mem_bigradedChainMinusPiece hc

/-- The graded differential agrees with the total differential after inclusion. -/
@[simp]
theorem coe_gradedUnblockedDifferential (R : Type*) [CommSemiring R] (a m : ℤ)
    (c : G.bigradedChainMinusPiece R (m + 1, a)) :
    (G.gradedUnblockedDifferential R a m c : GridChainMinus R n) =
      G.1.unblockedDifferential R c := (rfl)

/-- Multiplication by `V_i` between homogeneous pieces of `GC⁻`. -/
noncomputable def gradedUnblockedX (R : Type*) [CommSemiring R] (i : Fin n) (g : ℤ × ℤ) :
    G.bigradedChainMinusPiece R g →ₗ[R] G.bigradedChainMinusPiece R (g - (2, 1)) :=
  ((LinearMap.lsmul (MvPolynomial (Fin n) R) (GridChainMinus R n) (X i)).restrictScalars R).restrict
    fun _ hc => G.X_smul_mem_bigradedChainMinusPiece i hc

/-- Inclusion identifies the graded variable map with multiplication by that variable. -/
@[simp]
theorem coe_gradedUnblockedX (R : Type*) [CommSemiring R] (i : Fin n) (g : ℤ × ℤ)
    (c : G.bigradedChainMinusPiece R g) :
    (G.gradedUnblockedX R i g c : GridChainMinus R n) = (X i : MvPolynomial (Fin n) R) • c :=
  (rfl)

/-- Multiplication by a variable is injective on each homogeneous chain module. -/
theorem gradedUnblockedX_injective (R : Type*) [CommSemiring R] (i : Fin n) (g : ℤ × ℤ) :
    Function.Injective (G.gradedUnblockedX R i g) := by
  intro c d h
  apply Subtype.ext
  exact X_smul_gridChainMinus_injective R i
    (by simpa only [coe_gradedUnblockedX] using congrArg Subtype.val h)

/-- At every bidegree, the kernel of specialization at `V_i = 0` consists exactly
of the multiples of `V_i` coming from the piece two higher in Maslov and one higher
in Alexander. Together with injectivity and surjectivity, this is the degreewise
short exact sequence relating the unblocked and simply blocked chain modules. -/
theorem exact_gradedUnblockedX_gradedSimplyBlockedSpecialization
    (R : Type*) [CommSemiring R] (i : Fin n) (g : ℤ × ℤ) :
    Function.Exact (G.gradedUnblockedX R i g)
      (G.gradedSimplyBlockedSpecialization R i (g - (2, 1))) := by
  intro c
  constructor
  · intro hc
    have hz : simplyBlockedSpecialization R i (c : GridChainMinus R n) = 0 := by
      simpa only [coe_gradedSimplyBlockedSpecialization, ZeroMemClass.coe_zero]
        using congrArg Subtype.val hc
    obtain ⟨b, hb⟩ := (exact_X_smul_simplyBlockedSpecialization R i c.val).mp hz
    have hb' : (X i : MvPolynomial (Fin n) R) • b = c.val := hb
    have hgrade : b ∈ G.bigradedChainMinusPiece R g :=
      (G.X_smul_mem_bigradedChainMinusPiece_iff i).mp (by rw [hb']; exact c.2)
    exact ⟨⟨b, hgrade⟩, Subtype.ext hb'⟩
  · rintro ⟨b, rfl⟩
    apply Subtype.ext
    rw [coe_gradedSimplyBlockedSpecialization, ZeroMemClass.coe_zero, coe_gradedUnblockedX]
    exact (exact_X_smul_simplyBlockedSpecialization R i _).mpr ⟨b.val, rfl⟩

variable (R : Type*) [CommRing R] [CharP R 2]

/-- Consecutive graded unblocked differentials compose to zero. -/
theorem gradedUnblockedDifferential_comp_eq_zero (a m : ℤ) :
    (G.gradedUnblockedDifferential R a m).comp
      (G.gradedUnblockedDifferential R a (m + 1)) = 0 := by
  ext c : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, coe_gradedUnblockedDifferential,
    ZeroMemClass.coe_zero]
  exact LinearMap.congr_fun (G.1.unblockedDifferential_comp_self_eq_zero R) c

/-- The Maslov-graded unblocked grid complex in Alexander degree `a`. Its degree-`m`
homology is the unblocked grid homology in bidegree `(m, a)`. -/
noncomputable def gradedUnblockedComplex (a : ℤ) : ChainComplex (ModuleCat R) ℤ :=
  ChainComplex.of (fun m => ModuleCat.of R (G.bigradedChainMinusPiece R (m, a)))
    (fun m => ModuleCat.ofHom (G.gradedUnblockedDifferential R a m)) (fun m => by
      rw [← ModuleCat.ofHom_comp, G.gradedUnblockedDifferential_comp_eq_zero,
        ModuleCat.ofHom_zero])

/-- The objects of the graded complex are the homogeneous unblocked chain modules. -/
@[simp]
theorem gradedUnblockedComplex_X (a m : ℤ) :
    (G.gradedUnblockedComplex R a).X m =
      ModuleCat.of R (G.bigradedChainMinusPiece R (m, a)) := (rfl)

/-- The consecutive differential is the restriction of the total unblocked differential. -/
@[simp]
theorem gradedUnblockedComplex_d (a m : ℤ) :
    (G.gradedUnblockedComplex R a).d (m + 1) m =
      eqToHom (G.gradedUnblockedComplex_X R a (m + 1)) ≫
        ModuleCat.ofHom (G.gradedUnblockedDifferential R a m) ≫
          eqToHom (G.gradedUnblockedComplex_X R a m).symm := by
  simp only [gradedUnblockedComplex, ChainComplex.of_d]
  -- The object identifications act as identity maps on homogeneous chains.
  ext c
  rfl

/-- Specialization at `V_i = 0` as a chain map preserving both gradings. -/
noncomputable def gradedSimplyBlockedSpecializationMap (i : Fin n) (a : ℤ) :
    G.gradedUnblockedComplex R a ⟶ G.gradedSimplyBlockedComplex R i a :=
  ChainComplex.ofHom (fun m => eqToHom (G.gradedUnblockedComplex_X R a m) ≫
    ModuleCat.ofHom (R := R) (G.gradedSimplyBlockedSpecialization R i (m, a)) ≫
      eqToHom (G.gradedSimplyBlockedComplex_X R i a m).symm)
    (fun m => by
      rw [gradedUnblockedComplex_d, gradedSimplyBlockedComplex_d]
      apply (cancel_epi (eqToHom (G.gradedUnblockedComplex_X R a (m + 1)).symm)).mp
      apply (cancel_mono (eqToHom (G.gradedSimplyBlockedComplex_X R i a m))).mp
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        Category.comp_id, eqToHom_trans]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      apply Subtype.ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        coe_gradedSimplyBlockedSpecialization, coe_gradedUnblockedDifferential,
        coe_gradedSimplyBlockedDifferential]
      exact (G.1.simplyBlockedSpecialization_unblockedDifferential R i c).symm)

/-- The components of the specialization chain map are the homogeneous
coefficient-specialization maps, after identifying the complex objects. -/
@[simp]
theorem gradedSimplyBlockedSpecializationMap_f (i : Fin n) (a m : ℤ) :
    (G.gradedSimplyBlockedSpecializationMap R i a).f m =
      eqToHom (G.gradedUnblockedComplex_X R a m) ≫
        ModuleCat.ofHom (G.gradedSimplyBlockedSpecialization R i (m, a)) ≫
          eqToHom (G.gradedSimplyBlockedComplex_X R i a m).symm := (rfl)

/-- Every component of the specialization chain map is an epimorphism. -/
instance epi_gradedSimplyBlockedSpecializationMap_f (i : Fin n) (a m : ℤ) :
    Epi ((G.gradedSimplyBlockedSpecializationMap R i a).f m) := by
  let f : ModuleCat.of R (G.bigradedChainMinusPiece R (m, a)) ⟶
      ModuleCat.of R (G.bigradedChainHatPiece R i (m, a)) :=
    ModuleCat.ofHom (G.gradedSimplyBlockedSpecialization R i (m, a))
  have : Epi f := by
    apply (ModuleCat.epi_iff_surjective f).mpr
    exact G.gradedSimplyBlockedSpecialization_surjective R i (m, a)
  exact inferInstanceAs (Epi
    (eqToHom (G.gradedUnblockedComplex_X R a m) ≫ f ≫
      eqToHom (G.gradedSimplyBlockedComplex_X R i a m).symm))

end TauCeti.OddComponentGridDiagram
