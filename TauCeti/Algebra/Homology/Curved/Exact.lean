/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Biproduct
public import TauCeti.Algebra.Homology.Curved.Limits
public import TauCeti.CategoryTheory.Exact.Functor

/-!
# The componentwise exact structure on curved duplexes

Let `E` be a Quillen exact structure on an `R`-linear additive category `C` and let `w : R`. The
category `CurvedDuplex C w` of curved duplexes of curvature `w` carries the **componentwise exact
structure** `E.curvedDuplex w`: a short complex of curved duplexes is a conflation when its even
and its odd components are conflations of `E`. No limits or colimits are assumed in `C`: the
kernels, cokernels, pushouts and pullbacks required by the axioms are those supplied
componentwise by `E`, assembled into curved duplexes by the componentwise limits and colimits
of `TauCeti.Algebra.Homology.Curved.Limits`.

Specializing `E` to the split exact structure gives the **componentwise split** exact structure
`(ExactStructure.split C).curvedDuplex w`, whose conflations are the short complexes of curved
duplexes which split in both components, though not necessarily compatibly with the
differentials. It is Frobenius, with the contractible duplexes as its projective-injective
objects (`TauCeti.ExactStructure.curvedDuplex_split_isFrobenius`).

## Main definitions

* `TauCeti.ExactStructure.curvedDuplex`: the componentwise exact structure on
  `CurvedDuplex C w`.

## Main results

* `TauCeti.CurvedDuplex.isKernelCokernelPair_of_eval`: a short complex of curved duplexes which is
  a kernel–cokernel pair in both components is a kernel–cokernel pair.
* `TauCeti.ExactStructure.curvedDuplex_conflation_iff`,
  `TauCeti.ExactStructure.curvedDuplex_isInflation_iff` and
  `TauCeti.ExactStructure.curvedDuplex_isDeflation_iff`: conflations, inflations and deflations
  are detected componentwise.
* `TauCeti.ExactStructure.isConflationExact_eval₀_curvedDuplex` and
  `TauCeti.ExactStructure.isConflationExact_eval₁_curvedDuplex`: the evaluation functors
  preserve conflations.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Section 9, for the corresponding degreewise exact structure
  on chain complexes.
* I. Frenkel, M. Khovanov, O. Schiffmann, *Homological realization of Nakajima varieties and Weyl
  group actions*, Compos. Math. **141** (2005), 1479–1503, Sections 2–3, where curved complexes
  are given the componentwise split exact structure.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w' v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type w'} [Semiring R] [Linear R C]

namespace CurvedDuplex

variable {w : R}

/-- A short complex of curved duplexes which is a kernel–cokernel pair in both components is a
kernel–cokernel pair: kernels and cokernels of curved duplexes may be computed componentwise. -/
theorem isKernelCokernelPair_of_eval {S : ShortComplex (CurvedDuplex C w)}
    (h₀ : IsKernelCokernelPair (S.map (eval₀ C w)))
    (h₁ : IsKernelCokernelPair (S.map (eval₁ C w))) : IsKernelCokernelPair S where
  nonempty_fIsKernel := ⟨isLimitOfEval _ _
    ((isLimitMapConeForkEquiv' (eval₀ C w) S.zero).symm h₀.fIsKernel)
    ((isLimitMapConeForkEquiv' (eval₁ C w) S.zero).symm h₁.fIsKernel)⟩
  nonempty_gIsCokernel := ⟨isColimitOfEval _ _
    ((isColimitMapCoconeCoforkEquiv' (eval₀ C w) S.zero).symm h₀.gIsCokernel)
    ((isColimitMapCoconeCoforkEquiv' (eval₁ C w) S.zero).symm h₁.gIsCokernel)⟩

end CurvedDuplex

namespace ExactStructure

open CurvedDuplex

variable [HasZeroObject C] [HasBinaryBiproducts C] (E : ExactStructure C) (w : R)

/-- The componentwise conflation class on curved duplexes. -/
private def curvedDuplexConflationClass : ConflationClass (CurvedDuplex C w) where
  Conflation S := E.Conflation (S.map (eval₀ C w)) ∧ E.Conflation (S.map (eval₁ C w))
  isKernelCokernelPair _ hS :=
    isKernelCokernelPair_of_eval (E.isKernelCokernelPair _ hS.1) (E.isKernelCokernelPair _ hS.2)
  isClosedUnderIsomorphisms :=
    { of_iso := fun e hS =>
        ⟨E.conflation_of_iso ((eval₀ C w).mapShortComplex.mapIso e) hS.1,
          E.conflation_of_iso ((eval₁ C w).mapShortComplex.mapIso e) hS.2⟩ }

variable {E w}

/-- A morphism of curved duplexes which is an inflation in both components is the first map of
a componentwise conflation, whose second map is its cokernel in `CurvedDuplex C w`. -/
private theorem curvedDuplexConflationClass_isInflation_iff {X Y : CurvedDuplex C w}
    (f : X ⟶ Y) :
    (curvedDuplexConflationClass E w).IsInflation f ↔
      E.IsInflation f.f₀ ∧ E.IsInflation f.f₁ := by
  simp only [ConflationClass.isInflation_iff]
  constructor
  · rintro ⟨M, p, zero, hS₀, hS₁⟩
    exact ⟨⟨M.X₀, p.f₀, congrArg Hom.f₀ zero, hS₀⟩, ⟨M.X₁, p.f₁, congrArg Hom.f₁ zero, hS₁⟩⟩
  · intro ⟨hf₀, hf₁⟩
    -- In each component the conflation witnessing the inflation provides a cokernel, so `f` has
    -- a cokernel in curved duplexes which both evaluation functors preserve.
    have hcok (G : CurvedDuplex C w ⥤ C) [G.PreservesZeroMorphisms]
        (hG : ∃ (M : C) (p : G.obj Y ⟶ M) (zero : G.map f ≫ p = 0),
          E.Conflation (ShortComplex.mk _ _ zero)) :
        HasColimit (parallelPair f 0 ⋙ G) := by
      obtain ⟨M, p, zero, hS⟩ := hG
      have : HasCokernel (G.map f) := ⟨⟨⟨_, (E.isKernelCokernelPair _ hS).gIsCokernel⟩⟩⟩
      exact hasColimit_of_iso (F := parallelPair (G.map f) 0) (diagramIsoParallelPair _ ≪≫
        parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp))
    have := hcok (eval₀ C w) hf₀
    have := hcok (eval₁ C w) hf₁
    have hπ : IsColimit (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f)) :=
      cokernelIsCokernel f
    refine ⟨cokernel f, cokernel.π f, cokernel.condition f, ?_, ?_⟩
    · exact E.conflation_of_isColimit_of_isInflation
        ((isColimitMapCoconeCoforkEquiv' (eval₀ C w) (cokernel.condition f))
          (isColimitOfPreserves (eval₀ C w) hπ))
        ((ConflationClass.isInflation_iff _ _).2 hf₀)
    · exact E.conflation_of_isColimit_of_isInflation
        ((isColimitMapCoconeCoforkEquiv' (eval₁ C w) (cokernel.condition f))
          (isColimitOfPreserves (eval₁ C w) hπ))
        ((ConflationClass.isInflation_iff _ _).2 hf₁)

/-- A morphism of curved duplexes which is a deflation in both components is the second map of
a componentwise conflation, whose first map is its kernel in `CurvedDuplex C w`. -/
private theorem curvedDuplexConflationClass_isDeflation_iff {X Y : CurvedDuplex C w}
    (f : X ⟶ Y) :
    (curvedDuplexConflationClass E w).IsDeflation f ↔
      E.IsDeflation f.f₀ ∧ E.IsDeflation f.f₁ := by
  simp only [ConflationClass.isDeflation_iff]
  constructor
  · rintro ⟨M, i, zero, hS₀, hS₁⟩
    exact ⟨⟨M.X₀, i.f₀, congrArg Hom.f₀ zero, hS₀⟩, ⟨M.X₁, i.f₁, congrArg Hom.f₁ zero, hS₁⟩⟩
  · intro ⟨hf₀, hf₁⟩
    -- In each component the conflation witnessing the deflation provides a kernel, so `f` has
    -- a kernel in curved duplexes which both evaluation functors preserve.
    have hker (G : CurvedDuplex C w ⥤ C) [G.PreservesZeroMorphisms]
        (hG : ∃ (M : C) (i : M ⟶ G.obj X) (zero : i ≫ G.map f = 0),
          E.Conflation (ShortComplex.mk _ _ zero)) :
        HasLimit (parallelPair f 0 ⋙ G) := by
      obtain ⟨M, i, zero, hS⟩ := hG
      have : HasKernel (G.map f) := ⟨⟨⟨_, (E.isKernelCokernelPair _ hS).fIsKernel⟩⟩⟩
      exact hasLimit_of_iso (F := parallelPair (G.map f) 0)
        ((diagramIsoParallelPair _ ≪≫
          parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp) :
          parallelPair f 0 ⋙ G ≅ parallelPair (G.map f) 0)).symm
    have := hker (eval₀ C w) hf₀
    have := hker (eval₁ C w) hf₁
    have hι : IsLimit (KernelFork.ofι (kernel.ι f) (kernel.condition f)) := kernelIsKernel f
    refine ⟨kernel f, kernel.ι f, kernel.condition f, ?_, ?_⟩
    · exact E.conflation_of_isLimit_of_isDeflation
        ((isLimitMapConeForkEquiv' (eval₀ C w) (kernel.condition f))
          (isLimitOfPreserves (eval₀ C w) hι))
        ((ConflationClass.isDeflation_iff _ _).2 hf₀)
    · exact E.conflation_of_isLimit_of_isDeflation
        ((isLimitMapConeForkEquiv' (eval₁ C w) (kernel.condition f))
          (isLimitOfPreserves (eval₁ C w) hι))
        ((ConflationClass.isDeflation_iff _ _).2 hf₁)

variable (E w)

/-- **The componentwise exact structure on curved duplexes.** A short complex of curved
duplexes is a conflation when its even and its odd components are conflations of `E`. -/
noncomputable def curvedDuplex : ExactStructure (CurvedDuplex C w) where
  toConflationClass := curvedDuplexConflationClass E w
  isInflation_id X := (curvedDuplexConflationClass_isInflation_iff _).2
    ⟨E.isInflation_id X.X₀, E.isInflation_id X.X₁⟩
  isDeflation_id X := (curvedDuplexConflationClass_isDeflation_iff _).2
    ⟨E.isDeflation_id X.X₀, E.isDeflation_id X.X₁⟩
  isInflation_comp f g hf hg := by
    rw [curvedDuplexConflationClass_isInflation_iff] at hf hg ⊢
    exact ⟨E.isInflation_comp _ _ hf.1 hg.1, E.isInflation_comp _ _ hf.2 hg.2⟩
  isDeflation_comp f g hf hg := by
    rw [curvedDuplexConflationClass_isDeflation_iff] at hf hg ⊢
    exact ⟨E.isDeflation_comp _ _ hf.1 hg.1, E.isDeflation_comp _ _ hf.2 hg.2⟩
  hasPushouts_inflations :=
    { hasPushout := fun {_ _ _ f} g hf => by
        have hf' := (curvedDuplexConflationClass_isInflation_iff f).1 hf
        have := E.hasPushouts_inflations.hasPushout g.f₀ hf'.1
        have := E.hasPushouts_inflations.hasPushout g.f₁ hf'.2
        have := hasColimit_span_comp_eval₀ (f := f) (g := g)
        have := hasColimit_span_comp_eval₁ (f := f) (g := g)
        infer_instance }
  isStableUnderCobaseChange_inflations :=
    { of_isPushout := fun {_ _ _ _ f g _ _} sq hf => by
        have hf' := (curvedDuplexConflationClass_isInflation_iff f).1 hf
        have := E.hasPushouts_inflations.hasPushout g.f₀ hf'.1
        have := E.hasPushouts_inflations.hasPushout g.f₁ hf'.2
        have := hasPushout_symmetry f.f₀ g.f₀
        have := hasPushout_symmetry f.f₁ g.f₁
        have := hasColimit_span_comp_eval₀ (f := g) (g := f)
        have := hasColimit_span_comp_eval₁ (f := g) (g := f)
        exact (curvedDuplexConflationClass_isInflation_iff _).2
          ⟨E.isStableUnderCobaseChange_inflations.of_isPushout (sq.map (eval₀ C w)) hf'.1,
            E.isStableUnderCobaseChange_inflations.of_isPushout (sq.map (eval₁ C w)) hf'.2⟩ }
  hasPullbacks_deflations :=
    { hasPullback := fun {_ _ _ f} g hf => by
        have hf' := (curvedDuplexConflationClass_isDeflation_iff f).1 hf
        have := E.hasPullbacks_deflations.hasPullback g.f₀ hf'.1
        have := E.hasPullbacks_deflations.hasPullback g.f₁ hf'.2
        have := hasLimit_cospan_comp_eval₀ (f := f) (g := g)
        have := hasLimit_cospan_comp_eval₁ (f := f) (g := g)
        infer_instance }
  isStableUnderBaseChange_deflations :=
    { of_isPullback := fun {_ _ _ _ f g _ _} sq hg => by
        have hg' := (curvedDuplexConflationClass_isDeflation_iff g).1 hg
        have := E.hasPullbacks_deflations.hasPullback f.f₀ hg'.1
        have := E.hasPullbacks_deflations.hasPullback f.f₁ hg'.2
        have := hasLimit_cospan_comp_eval₀ (f := g) (g := f)
        have := hasLimit_cospan_comp_eval₁ (f := g) (g := f)
        exact (curvedDuplexConflationClass_isDeflation_iff _).2
          ⟨E.isStableUnderBaseChange_deflations.of_isPullback (sq.map (eval₀ C w)) hg'.1,
            E.isStableUnderBaseChange_deflations.of_isPullback (sq.map (eval₁ C w)) hg'.2⟩ }

/-- A short complex of curved duplexes is a conflation for the componentwise exact structure
exactly when both of its components are conflations. -/
@[simp]
theorem curvedDuplex_conflation_iff (S : ShortComplex (CurvedDuplex C w)) :
    (E.curvedDuplex w).Conflation S ↔
      E.Conflation (S.map (eval₀ C w)) ∧ E.Conflation (S.map (eval₁ C w)) :=
  Iff.rfl

variable {E w}

/-- A morphism of curved duplexes is an inflation for the componentwise exact structure exactly
when both of its components are inflations. -/
@[simp]
theorem curvedDuplex_isInflation_iff {X Y : CurvedDuplex C w} (f : X ⟶ Y) :
    (E.curvedDuplex w).IsInflation f ↔ E.IsInflation f.f₀ ∧ E.IsInflation f.f₁ :=
  curvedDuplexConflationClass_isInflation_iff f

/-- A morphism of curved duplexes is a deflation for the componentwise exact structure exactly
when both of its components are deflations. -/
@[simp]
theorem curvedDuplex_isDeflation_iff {X Y : CurvedDuplex C w} (f : X ⟶ Y) :
    (E.curvedDuplex w).IsDeflation f ↔ E.IsDeflation f.f₀ ∧ E.IsDeflation f.f₁ :=
  curvedDuplexConflationClass_isDeflation_iff f

variable (E w)

/-- Evaluation at the even component preserves conflations of the componentwise exact
structure. -/
theorem isConflationExact_eval₀_curvedDuplex :
    (E.curvedDuplex w).IsConflationExact E (eval₀ C w) :=
  ⟨fun hS => hS.1⟩

/-- Evaluation at the odd component preserves conflations of the componentwise exact
structure. -/
theorem isConflationExact_eval₁_curvedDuplex :
    (E.curvedDuplex w).IsConflationExact E (eval₁ C w) :=
  ⟨fun hS => hS.2⟩

end ExactStructure

end TauCeti
