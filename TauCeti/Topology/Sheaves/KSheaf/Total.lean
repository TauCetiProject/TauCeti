/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.TotalComplex.Functor
public import TauCeti.Topology.Sheaves.KSheaf.ShortExact

/-!
# Total complexes of finite sequences of homotopy K-sheaves

A finite sequence `F_a ⟶ F_(a+1) ⟶ ⋯ ⟶ F_b` of K-presheaves of cochain complexes whose adjacent
maps compose to zero is a K-presheaf `F` of double complexes indexed by `ℤ × ℤ` whose columns
`K ↦ (F K).X p` vanish for `p ∉ [a, b]`. Its total complex
`K ↦ Tot (F K)`, in degree `n` the sum of the `(F K).X p` in degree `n - p`, is the K-presheaf
`F.totalComplex (ComplexShape.up ℤ)` (`CategoryTheory.Functor.totalComplex`).

**Pardon's Lemma A.2.11** (`TopCat.KPresheaf.isHomotopyKSheaf_totalComplex`). If every column of
`F` is a homotopy K-sheaf, then so is the total complex. For two columns this is the case of
mapping cones (`TopCat.KPresheaf.isHomotopyKSheaf_mappingConeFunctor`). Virtual cochain complexes
of implicit atlases are assembled from homotopy K-sheaves by such finite totals, for instance the
flag totals of interval diagrams, and this lemma is what keeps them homotopy K-sheaves.

The proof is an induction on the number of columns. The brutal truncations of `F` in its columns
give the short exact sequence `σ^{≥ a + 1} F ⟶ F ⟶ σ^{≤ a} F`
(`CategoryTheory.Functor.stupidTruncShortComplex`), split in each bidegree, hence a
short exact sequence of total complexes
(`CategoryTheory.ShortComplex.shortExact_totalComplex`); homotopy K-sheaves are closed under
extensions (`CategoryTheory.ShortComplex.ShortExact.isHomotopyKSheaf_X₂`). The total complex of
the last term, concentrated in the column `a`, is that column shifted by `-a`
(`CategoryTheory.Functor.shiftIsoTotalComplexOfIsZero`), and shifts of homotopy K-sheaves are
homotopy K-sheaves (`TopCat.KPresheaf.IsHomotopyKSheaf.comp_shiftFunctor`).

## Main results

* `TopCat.KPresheaf.isHomotopyKSheaf_totalComplex`: the total complex of a K-presheaf of double
  complexes with finitely many nonzero columns, all homotopy K-sheaves, is a homotopy K-sheaf.

## References

* J. Pardon, *An algebraic approach to virtual fundamental cycles on moduli spaces of
  pseudo-holomorphic curves*, Geom. Topol. 20 (2016), Appendix A.2, Definition A.2.5 and
  Lemma A.2.11.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace HomologicalComplex

universe w v u

namespace TopCat.KPresheaf

variable {X : TopCat.{w}} [T2Space X] {C : Type u} [Category.{v} C] [Abelian C]
  [HasFilteredColimitsOfSize.{w, w} C] [AB5OfSize.{w, w} C] [WeaklyLocallyCompactSpace X]

/-- A K-presheaf of double complexes concentrated in the column `c`, which is a homotopy K-sheaf,
has a homotopy K-sheaf as total complex: the column shifted by `-c`. -/
private theorem isHomotopyKSheaf_totalComplex_of_isZero
    (F : KPresheaf (HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) X)
    [∀ K, (F.obj K).HasTotal (ComplexShape.up ℤ)] (c : ℤ)
    (hF : ∀ K p, p ≠ c → IsZero ((F.obj K).X p))
    (hc : IsHomotopyKSheaf (F ⋙ HomologicalComplex.eval _ _ c)) :
    IsHomotopyKSheaf (F.totalComplex (ComplexShape.up ℤ)) :=
  (hc.comp_shiftFunctor (-c)).of_iso (F.shiftIsoTotalComplexOfIsZero c hF)

/-- Pardon's Lemma A.2.11 for the columns `[a, a + k]`, by induction on `k`. -/
private theorem isHomotopyKSheaf_totalComplex_aux (k : ℕ) :
    ∀ (a : ℤ) (F : KPresheaf (HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) X)
      [∀ K, (F.obj K).HasTotal (ComplexShape.up ℤ)],
      (∀ K p, p < a ∨ a + k < p → IsZero ((F.obj K).X p)) →
      (∀ p, IsHomotopyKSheaf (F ⋙ HomologicalComplex.eval _ _ p)) →
      IsHomotopyKSheaf (F.totalComplex (ComplexShape.up ℤ)) := by
  induction k with
  | zero =>
    intro a F _ hF hcol
    exact isHomotopyKSheaf_totalComplex_of_isZero F a (fun K p hp ↦ hF K p (by omega)) (hcol a)
  | succ k ih =>
    intro a F _ hF hcol
    -- Split off the column `a` by the short exact sequence `σ^{≥ a + 1} F ⟶ F ⟶ σ^{≤ a} F`.
    set S : ShortComplex (KPresheaf (HomologicalComplex₂ C (.up ℤ) (.up ℤ)) X) :=
      F.stupidTruncShortComplex a with hS
    -- `S.X₁.obj K`, `S.X₃.obj K` are truncations of `F.obj K` (`stupidTruncShortComplex_X₁`)
    have h₁ : ∀ K p, p < a + 1 ∨ a + 1 + k < p → IsZero ((S.X₁.obj K).X p) := fun K p hp ↦
      CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X_of_isZero (F.obj K) (a + 1)
        (a + 1 + k) (fun q hq ↦ hF K q (by omega)) hp
    have h₃ : ∀ K p, p ≠ a → IsZero ((S.X₃.obj K).X p) := fun K p hp ↦
      CochainComplex.isZero_stupidTrunc_embeddingUpIntLE_X_of_isZero (F.obj K) a a
        (fun q hq ↦ hF K q (by omega)) (by omega)
    have : ∀ K, (S.X₁.obj K).HasTotal (ComplexShape.up ℤ) := fun K ↦
      HomologicalComplex₂.hasTotal_of_isZero_X _ (a + 1) (a + 1 + k) (h₁ K)
    have : ∀ K, (S.X₂.obj K).HasTotal (ComplexShape.up ℤ) := fun K ↦
      inferInstanceAs ((F.obj K).HasTotal _)
    have : ∀ K, (S.X₃.obj K).HasTotal (ComplexShape.up ℤ) := fun K ↦
      HomologicalComplex₂.hasTotal_of_isZero_X _ a a fun p hp ↦ h₃ K p (by omega)
    -- The columns `p ≥ a + 1` of `σ^{≥ a + 1} F` are those of `F`, the others vanish.
    have hcol₁ (p : ℤ) : IsHomotopyKSheaf (S.X₁ ⋙ HomologicalComplex.eval _ _ p) := by
      by_cases hp : a + 1 ≤ p
      · have : ∀ K, IsIso ((Functor.whiskerRight S.f (HomologicalComplex.eval _ _ p)).app K) :=
          fun K ↦ by
            dsimp [S]
            exact (F.obj K).isIso_ιStupidTrunc_f
              (ComplexShape.embeddingUpIntGE (a + 1)) (i := (p - (a + 1)).toNat) (by simp; omega)
        have := NatIso.isIso_of_isIso_app (Functor.whiskerRight S.f (HomologicalComplex.eval _ _ p))
        exact (hcol p).of_iso (asIso (Functor.whiskerRight S.f _)).symm
      · exact isHomotopyKSheaf_of_acyclic fun K ↦ acyclic_of_isZero _ (h₁ (op K) p (by omega))
    -- The column `a` of `σ^{≤ a} F` is that of `F`.
    have hcol₃ : IsHomotopyKSheaf (S.X₃ ⋙ HomologicalComplex.eval _ _ a) := by
      have : ∀ K, IsIso ((Functor.whiskerRight S.g (HomologicalComplex.eval _ _ a)).app K) :=
        fun K ↦ by
          dsimp [S]
          exact (F.obj K).isIso_πStupidTrunc_f (ComplexShape.embeddingUpIntLE a) (i := 0) (by simp)
      have := NatIso.isIso_of_isIso_app (Functor.whiskerRight S.g (HomologicalComplex.eval _ _ a))
      exact (hcol a).of_iso (asIso (Functor.whiskerRight S.g _))
    refine (S.shortExact_totalComplex (ComplexShape.up ℤ) fun K p q ↦ ?_).isHomotopyKSheaf_X₂
      (ih (a + 1) S.X₁ h₁ hcol₁) (isHomotopyKSheaf_totalComplex_of_isZero S.X₃ a h₃ hcol₃)
    rw [hS, Functor.stupidTruncShortComplex_map_evaluation]
    exact (CochainComplex.stupidTruncShortComplexSplitting (F.obj K) a p).map _

/-- **Pardon, Lemma A.2.11.** Let `F` be a K-presheaf of double complexes indexed by `ℤ × ℤ`, that
is a sequence `⋯ ⟶ F_p ⟶ F_(p+1) ⟶ ⋯` of K-presheaves of cochain complexes `F_p = (F -).X p`
whose adjacent maps compose to zero, and suppose that `F_p = 0` for `p ∉ [a, b]`. If every
`F_p` with `a ≤ p ≤ b` is a homotopy K-sheaf, then the total complex
`K ↦ Tot (F K)` is a homotopy K-sheaf. -/
theorem isHomotopyKSheaf_totalComplex
    (F : KPresheaf (HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) X)
    [∀ K, (F.obj K).HasTotal (ComplexShape.up ℤ)] (a b : ℤ)
    (hF : ∀ K p, p < a ∨ b < p → IsZero ((F.obj K).X p))
    (hcol : ∀ p, a ≤ p → p ≤ b → IsHomotopyKSheaf (F ⋙ HomologicalComplex.eval _ _ p)) :
    IsHomotopyKSheaf (F.totalComplex (ComplexShape.up ℤ)) :=
  isHomotopyKSheaf_totalComplex_aux (b - a).toNat a F (fun K p hp ↦ hF K p (by omega)) fun p ↦
    if hp : a ≤ p ∧ p ≤ b then hcol p hp.1 hp.2
    else isHomotopyKSheaf_of_acyclic fun K ↦ acyclic_of_isZero _ (hF (op K) p (by omega))

end TopCat.KPresheaf
