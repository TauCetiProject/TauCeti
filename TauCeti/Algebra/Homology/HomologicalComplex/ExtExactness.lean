/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Category.Grp.Zero

/-!
# A cohomology vanishing criterion for nonnegative complexes

If a cochain complex is exact before degree `i`, the quotient of its term in degree `i` by
the incoming boundaries has a resolution by the first `i + 1` terms. The covariant long exact
sequence of `Ext` transfers vanishing in one degree along this resolution. Applying it with
the cohomology in degree `i` as the source kills the inclusion of this cohomology into that
quotient. This gives a criterion for exactness through a specified degree.

## References

* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280,
  Lemma 2.1 and the proof of the main theorem on p. 277.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- If `K` is exact below `i`, then vanishing of `Ext^(m + i - j)(X, K^j)` for all
`j ≤ i` implies vanishing of `Ext^m(X, K.opcycles i)`. -/
theorem subsingleton_ext_opcycles (K : CochainComplex C ℕ) (X : C) (i m : ℕ)
    (hK : ∀ j < i, K.ExactAt j)
    (h : ∀ j ≤ i, Subsingleton (Ext.{w} X (K.X j) (m + i - j))) :
    Subsingleton (Ext.{w} X (K.opcycles i) m) := by
  induction i generalizing m with
  | zero =>
      have : Subsingleton (Ext.{w} X (K.X 0) m) := by simpa using h 0 le_rfl
      exact AddCommGrpCat.isZero_iff_subsingleton.mp
        ((AddCommGrpCat.isZero_iff_subsingleton.mpr this).of_iso
          ((extFunctorObj X m).mapIso (K.opcycles₀Iso)).symm)
  | succ i ih =>
      have hprev : Subsingleton (Ext.{w} X (K.opcycles i) (m + 1)) := by
        apply ih (m + 1) (fun j hj ↦ hK j (by omega))
        intro j hj
        rw [Nat.add_assoc, Nat.add_comm 1 i]
        exact h j (hj.trans (Nat.le_succ i))
      have hterm : Subsingleton (Ext.{w} X (K.X (i + 1)) m) := by
        simpa using h (i + 1) le_rfl
      have hmono : Mono (K.fromOpcycles i (i + 1)) :=
        Preadditive.mono_of_isZero_kernel' _ (K.homologyIsKernel i (i + 1) (by simp))
          (hK i (Nat.lt_succ_self i)).isZero_homology
      have hw : K.fromOpcycles i (i + 1) ≫ K.pOpcycles (i + 1) = 0 := by
        rw [← cancel_epi (K.pOpcycles i), p_fromOpcycles_assoc, d_pOpcycles, comp_zero]
      have hc := CokernelCofork.IsColimit.ofπ' (K.pOpcycles (i + 1)) hw (fun k hk ↦
        ⟨K.descOpcycles k i (by simp) (by rw [← p_fromOpcycles_assoc, hk, comp_zero]), by simp⟩)
      let S := ShortComplex.mk (K.fromOpcycles i (i + 1)) (K.pOpcycles (i + 1)) hw
      have hS : S.ShortExact :=
        ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel S hc) hmono inferInstance
      refine subsingleton_of_forall_eq 0 fun e ↦ ?_
      obtain ⟨f, hf⟩ := Ext.covariant_sequence_exact₃ X hS e (n₁ := m + 1) rfl
        (Subsingleton.elim _ _)
      simpa [Subsingleton.elim f 0] using hf.symm

/-- A nonnegative cochain complex is exact through degree `n` if, for every `i ≤ n`, its
`i`-th cohomology has vanishing `Ext^(i - j)` into the term in degree `j` for all `j ≤ i`.
In particular the hypothesis at `j = i` is the vanishing of `Hom(H^i, K^i)`. -/
theorem exactAt_of_subsingleton_ext_homology (K : CochainComplex C ℕ) {n : ℕ}
    (h : ∀ i ≤ n, ∀ j ≤ i, Subsingleton (Ext.{w} (K.homology i) (K.X j) (i - j))) :
    ∀ i ≤ n, K.ExactAt i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
      intro hi
      have : Subsingleton (Ext.{w} (K.homology i) (K.opcycles i) 0) :=
        K.subsingleton_ext_opcycles _ i 0
          (fun j hj ↦ ih j hj (hj.le.trans hi)) (by simpa using h i hi)
      have : Subsingleton (K.homology i ⟶ K.opcycles i) :=
        Ext.addEquiv₀.symm.toEquiv.subsingleton
      exact (K.exactAt_iff_isZero_homology i).mpr <|
        (IsZero.iff_id_eq_zero _).mpr <|
          (cancel_mono (K.homologyι i)).mp (Subsingleton.elim _ _)

end CochainComplex
