/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.SmoothCircle.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance

/-!
# Concordance of smooth circle presentations

The geometric knot presentation in the geometric-topology roadmap is a smooth embedding of the
oriented circle.  `SmoothEmbedding.Concordance` already gives the collared annulus in the product
with `ℝ`; this module makes its restriction to circle presentations the public interface used by
the concordance layer.  The relation is deliberately inherited from that generic construction,
so its ambient dimension and smoothness hypotheses remain visible at the point where they are
needed.

The resulting setoid identifies presentations by a smooth concordance.  Reparametrizing the
source circle or transporting the ambient manifold by a diffeomorphism preserves concordance.
These are the functoriality facts needed before forming the connected-sum quotient and its group
structure.

The smooth concordance relation here is the smooth variant.  The locally flat variant will use
the analogous topological annulus once the layer-2 and layer-6 topological inputs are assembled.

The definitions follow Livingston, *A survey of classical knot concordance*, in *Handbook of Knot
Theory* (2005), §1.
-/

public section

noncomputable section

namespace TauCeti

open scoped Manifold ContDiff

namespace SmoothCircleEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### The specialized relation and setoid -/

/-- A smooth concordance of two smooth circle presentations.

This is the generic collared concordance of smooth embeddings, specialized to source `Circle` and
smoothness `∞`.  It is an embedding of `Circle × ℝ` into `M × ℝ`, fixed in collars near the two
ends, and with the time coordinate in `(0, 1)` in the interior. -/
abbrev Concordance (f g : SmoothCircleEmbedding I M) : Type _ :=
  SmoothEmbedding.Concordance f g

/-- The smooth concordance relation on smooth circle presentations. -/
abbrev Concordant (f g : SmoothCircleEmbedding I M) : Prop :=
  SmoothEmbedding.Concordant f g

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- A concordance witnesses the specialized concordance relation. -/
theorem Concordance.concordant {f g : SmoothCircleEmbedding I M}
    (F : Concordance f g) : Concordant f g :=
  SmoothEmbedding.Concordant.of_concordance F

omit [FiniteDimensional ℝ E] in
/-- Smooth concordance of circle presentations is reflexive. -/
@[refl]
theorem Concordant.refl (f : SmoothCircleEmbedding I M) : Concordant f f :=
  SmoothEmbedding.Concordant.refl f

omit [FiniteDimensional ℝ E] in
/-- Smooth concordance of circle presentations is symmetric. -/
@[symm]
theorem Concordant.symm {f g : SmoothCircleEmbedding I M} (hfg : Concordant f g) :
    Concordant g f :=
  SmoothEmbedding.Concordant.symm hfg

/-- Smooth concordance of circle presentations is transitive. -/
@[trans]
theorem Concordant.trans {f g h : SmoothCircleEmbedding I M} (hfg : Concordant f g)
    (hgh : Concordant g h) : Concordant f h :=
  SmoothEmbedding.Concordant.trans hfg hgh

/-- Smooth concordance is an equivalence relation on geometric circle presentations. -/
theorem Concordant.equivalence :
    Equivalence (Concordant (I := I) (M := M)) :=
  ⟨Concordant.refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- The quotient relation used for the smooth concordance classes of circle presentations. -/
def concordanceSetoid (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] :
    Setoid (SmoothCircleEmbedding I M) where
  r := Concordant
  iseqv := Concordant.equivalence

/-- The relation of `concordanceSetoid` is smooth concordance. -/
@[simp]
theorem concordanceSetoid_r_iff (f g : SmoothCircleEmbedding I M) :
    (concordanceSetoid I M).r f g ↔ Concordant f g := Iff.rfl

/-! ### Functoriality -/

variable {P : Type*} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Ambient diffeomorphisms transport smooth concordances of circle presentations. -/
theorem Concordant.transDiffeomorph {f g : SmoothCircleEmbedding I M}
    (hfg : Concordant f g) (e : M ≃ₘ⟮I, I⟯ P) :
    Concordant (SmoothEmbedding.transDiffeomorph f e)
      (SmoothEmbedding.transDiffeomorph g e) :=
  SmoothEmbedding.Concordant.transDiffeomorph hfg e

omit [IsManifold I ∞ M] [FiniteDimensional ℝ E] in
/-- Reparametrizing a circle presentation by a smooth self-diffeomorphism preserves concordance. -/
theorem Concordant.compDiffeomorph {f g : SmoothCircleEmbedding I M}
    (hfg : Concordant f g) (e : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) :
    Concordant (SmoothEmbedding.compDiffeomorph f e)
      (SmoothEmbedding.compDiffeomorph g e) :=
  SmoothEmbedding.Concordant.compDiffeomorph hfg e

omit [FiniteDimensional ℝ E] in
/-- A smooth ambient isotopy of circle presentations gives a smooth concordance. -/
theorem SmoothAmbientIsotopic.concordant {f g : SmoothCircleEmbedding I M}
    (hfg : SmoothEmbedding.SmoothAmbientIsotopic f g) : Concordant f g :=
  SmoothEmbedding.SmoothAmbientIsotopic.concordant le_rfl hfg

end SmoothCircleEmbedding

end TauCeti

end
