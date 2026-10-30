/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Bifunctor.TwoTermSupport
public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence
public import TauCeti.Algebra.Homology.Monoidal.Homology.Connecting
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# K-flat cochain complexes

A cochain complex is K-flat if tensoring it with any acyclic complex is acyclic.
Flatness of an object is expressed by exactness of its tensor functor. A flat object
in any integer degree is K-flat, and a bounded complex of flat objects is K-flat.
The statements apply to modules and to sheaves of modules without choosing points
of the underlying site.

The tensor factor containing the K-flat complex is placed on the left. In a symmetric
monoidal category this is the usual K-flat condition, with the two factors interchanged
by the Koszul symmetry.

## References

* The Stacks Project, Cohomology on Sites, Section 21.17, Flat resolutions.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ K L : CochainComplex C ℤ, HasTensor K L]

namespace CochainComplex

/-- A complex is K-flat if tensoring it on the left preserves acyclicity. -/
class IsKFlat (K : CochainComplex C ℤ) : Prop where
  /-- Tensoring a K-flat complex with an acyclic complex gives an acyclic complex. -/
  acyclic_tensor (A : CochainComplex C ℤ) : A.Acyclic → (tensorObj K A).Acyclic

/-- The characteristic acyclicity criterion for K-flatness. -/
lemma isKFlat_iff (K : CochainComplex C ℤ) :
    K.IsKFlat ↔ ∀ A : CochainComplex C ℤ, A.Acyclic → (tensorObj K A).Acyclic :=
  ⟨fun h ↦ h.acyclic_tensor, fun h ↦ ⟨h⟩⟩

/-- K-flatness is invariant under an isomorphism of complexes. -/
lemma isKFlat_of_iso {K L : CochainComplex C ℤ} (e : K ≅ L) [K.IsKFlat] :
    L.IsKFlat := by
  constructor
  intro A hA i
  exact ExactAt.of_iso (IsKFlat.acyclic_tensor A hA i)
    (((curriedTensor C).map₂CochainComplex.flip.obj A).mapIso e)

end CochainComplex

namespace CategoryTheory.ShortComplex.ShortExact

/-- K-flatness is preserved by degreewise split extensions of complexes. -/
theorem isKFlat_X₂ {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) [∀ i, IsSplitMono (S.f.f i)]
    [S.X₁.IsKFlat] [S.X₃.IsKFlat] : S.X₂.IsKFlat := by
  constructor
  intro A hA
  exact (shortExact_tensorRightShortComplex A S hS).acyclic_X₂
    (CochainComplex.IsKFlat.acyclic_tensor A hA) (CochainComplex.IsKFlat.acyclic_tensor A hA)

end CategoryTheory.ShortComplex.ShortExact

namespace CochainComplex

/-- A flat object placed in any integer degree is K-flat. -/
theorem isKFlat_single_of_flat (M : C) (n : ℤ)
    [PreservesFiniteLimits (tensorLeft M)] [PreservesFiniteColimits (tensorLeft M)] :
    IsKFlat ((single C (.up ℤ) n).obj M) := by
  constructor
  intro A hA i
  let e := ((curriedTensor C).mapBifunctorSingleRowNatIso M n).app A
  refine ExactAt.of_iso (L := tensorObj ((single C (.up ℤ) n).obj M) A) ?_ e.symm
  exact (exactAt_shift_iff (((tensorLeft M).mapHomologicalComplex (.up ℤ)).obj A)
    (-n) i (-n + i) rfl).2 ((hA _).map (tensorLeft M))

section Bounded

variable [∀ M : C, PreservesFiniteColimits (tensorLeft M)]

private theorem isKFlat_of_bounded_flat_aux (a : ℤ) (n : ℕ) :
    ∀ (K : CochainComplex C ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE (a + n)],
      (∀ i, a ≤ i → i ≤ a + n → PreservesFiniteLimits (tensorLeft (K.X i))) →
        K.IsKFlat := by
  induction n with
  | zero =>
    intro K hge hle hflat
    have : K.IsStrictlyLE a := by simpa using hle
    obtain ⟨M, ⟨e⟩⟩ := exists_iso_single K a
    let eM : K.X a ≅ M := (eval C (.up ℤ) a).mapIso e ≪≫ singleObjXSelf (.up ℤ) a M
    have := hflat a le_rfl (by simp)
    have : PreservesFiniteLimits (tensorLeft M) :=
      preservesFiniteLimits_of_natIso ((curriedTensor C).mapIso eM)
    have := isKFlat_single_of_flat M a
    exact isKFlat_of_iso e.symm
  | succ n ih =>
    intro K hge hle hflat
    let b : ℤ := a + n
    have : K.IsStrictlyLE (b + 1) := by simpa [b, Nat.cast_add, Nat.cast_one, add_assoc] using hle
    let T : CochainComplex C ℤ := K.stupidTrunc (ComplexShape.embeddingUpIntLE b)
    have : T.IsStrictlyGE a := inferInstance
    have : T.IsStrictlyLE (a + n) := inferInstanceAs (T.IsStrictlyLE b)
    have : T.IsKFlat := ih T fun i hai hib ↦ by
      obtain ⟨j, hj⟩ : ∃ j, (ComplexShape.embeddingUpIntLE b).f j = i := by
        exact not_forall_not.mp fun h ↦
          (not_lt_of_ge hib) ((ComplexShape.notMem_range_embeddingUpIntLE_iff b i).1 h)
      have := hflat i hai (by omega)
      exact preservesFiniteLimits_of_natIso
        ((curriedTensor C).mapIso (K.stupidTruncXIso (ComplexShape.embeddingUpIntLE b) hj).symm)
    have : PreservesFiniteLimits (tensorLeft (K.X (b + 1))) :=
      hflat (b + 1) (by dsimp [b]; omega) (by dsimp [b]; omega)
    have := isKFlat_single_of_flat (K.X (b + 1)) (b + 1)
    have hS : (K.topShortComplex b).ShortExact :=
      shortExact_of_degreewise_shortExact _ fun i ↦ (K.topShortComplexSplitting b i).shortExact
    have (i : ℤ) : IsSplitMono ((K.topShortComplex b).f.f i) :=
      (K.topShortComplexSplitting b i).isSplitMono_f
    have : (K.topShortComplex b).X₁.IsKFlat := by
      rw [topShortComplex_X₁]
      infer_instance
    have : (K.topShortComplex b).X₃.IsKFlat := by
      rw [topShortComplex_X₃]
      exact inferInstanceAs T.IsKFlat
    simpa only [topShortComplex_X₂] using hS.isKFlat_X₂

/-- A bounded cochain complex of flat objects is K-flat. The bounds concern the actual terms,
rather than only the homology objects. -/
theorem isKFlat_of_bounded_flat (K : CochainComplex C ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b]
    [∀ i, PreservesFiniteLimits (tensorLeft (K.X i))] : K.IsKFlat := by
  have : K.IsStrictlyLE (a + (b - a).natAbs) :=
    isStrictlyLE_of_le K b _ (by have := Int.le_natAbs (a := b - a); omega)
  exact isKFlat_of_bounded_flat_aux a (b - a).natAbs K fun _ _ _ ↦ inferInstance

end Bounded

end CochainComplex
