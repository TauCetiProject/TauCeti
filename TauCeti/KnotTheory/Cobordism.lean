/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Data.ENat.Lattice
public import TauCeti.Geometry.Manifold.Instances.Cylinder
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.KnotTheory.SmoothCircle

import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
import TauCeti.AlgebraicTopology.Singular.Torus.Exterior
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# Knot cobordisms and the cobordism distance

Two knots `K₀`, `K₁ ⊆ S³` are related by a **cobordism of genus `g`** when they cobound a compact,
connected, orientable surface of genus `g` smoothly and properly embedded in `S³ × [0, 1]`, with
`K₀` in `S³ × {0}` and `K₁` in `S³ × {1}`. The least such genus is the **cobordism distance**
between the two knots. A concordance, an embedded annulus, is a cobordism of genus `0`. Classically,
capping off with a disc shows that the cobordism distance from `K` to the unknot is the slice genus
of `K`; that comparison needs gluing surfaces and is not formalized here.

As for knot concordance (`TauCeti.SmoothEmbedding.Concordance`), the surface is recorded in
collared form, which avoids manifolds with boundary: a knot cobordism from `K₀` to `K₁`
(`TauCeti.KnotCobordism K₀ K₁`) consists of

* a connected, orientable smooth surface `S` without boundary;
* a smooth embedding `Φ : S → Sⁿ × ℝ`, such that the part `Φ⁻¹ (Sⁿ × [0, 1])` of `S` over the
  slab is compact;
* such that for some `ε > 0` the image of `Φ` is the cylinder `K₀ × (-∞, ε]` at heights at most
  `ε`, and the cylinder `K₁ × [1 - ε, ∞)` at heights at least `1 - ε`.

The knots are smooth circle embeddings `K : S¹ → Sⁿ` into the unit sphere of an
`(n + 1)`-dimensional real inner product space `E`, with `S³ ⊆ ℝ⁴` the case `n = 3`. Only their
images enter (`TauCeti.KnotCobordism.congrRange`). The part of `S` over the slab is a compact
surface whose boundary is the two circles over the levels `0` and `1`, and `S` is that compact
surface with open collars attached along its boundary. The surface is modelled on `ℝ¹ × ℝ`, the
model of the cylinder `S¹ × ℝ` carrying the track of a concordance, so that a concordance is a
cobordism as it stands (`TauCeti.KnotCobordism.ofConcordance`).

The **genus** of a knot cobordism (`TauCeti.KnotCobordism.genus`) is read off its rational singular
homology, as for slice surfaces (`TauCeti.SliceSurfaceData.genus`): `S` deformation retracts onto
its compact part over the slab, a compact, connected, orientable surface of genus `g` with two
boundary circles, so `H₁(S; ℚ) ≅ ℚ²ᵍ⁺¹` and the genus is `⌊dim H₁(S; ℚ) / 2⌋`. The cylinder
`S¹ × ℝ` has `H₁ ≅ ℚ`, so a concordance has genus `0`
(`TauCeti.KnotCobordism.genus_ofConcordance`). The cobordism distance
(`TauCeti.cobordismDistance K₀ K₁`) is the infimum of the genera of the knot cobordisms from `K₀`
to `K₁`, valued in `ℕ∞` so that it is `⊤` when there is none; it vanishes on concordant knots
(`TauCeti.SmoothEmbedding.Concordant.cobordismDistance_eq_zero`). The converse, that a cobordism of
genus `0` is an annulus, needs the classification of compact surfaces and is not proved here.

Two operations keep the surface and move only its embedding, so they keep the genus. Reflecting
the heights by `t ↦ 1 - t` reverses a cobordism from `K₀` to `K₁` into one from `K₁` to `K₀`
(`TauCeti.KnotCobordism.symm`), so the cobordism distance is symmetric
(`TauCeti.cobordismDistance_comm`). A diffeomorphism `Ψ` of the ambient spheres, times the identity
of the height, transports a cobordism to one between the transported knots
(`TauCeti.KnotCobordism.transDiffeomorph`), so the cobordism distance is invariant under ambient
diffeomorphisms (`TauCeti.cobordismDistance_transDiffeomorph`); for the mirror image this is
`TauCeti.cobordismDistance_mirror` in `TauCeti.KnotTheory.Mirror`.

A concordance can be composed with a cobordism without changing the surface either. If `S` is a
cobordism from `K₀` to `K₁`, its top is the cylinder over `K₁` from some height `1 - 2 c` on. Up to
height `1 - c` the composite with a concordance `C` from `K₁` to `K₂` embeds the surface as `S`
does. Above that height it reads each point `S x = (K₁ z, t)` of the cylinder through its parameters
`(z, t)` and sends it to the point of the annulus of `C` at `(z, (t - (1 - c)) / c)`, its height
rescaled into `[1 - c, 1]` (`TauCeti.KnotCobordism.transConcordance`). The parameters depend
smoothly on `x` because `K₁` is an immersion and a topological embedding, so the composite is again
a smooth embedding. Composing on the other side reverses the cobordism, composes and reverses back
(`TauCeti.SmoothEmbedding.Concordance.transKnotCobordism`). Both keep the genus, so the cobordism
distance only depends on the concordance classes of the two knots
(`TauCeti.cobordismDistance_congr_concordant`). This is the genus-`0` case of the triangle
inequality. The general triangle inequality stacks two cobordisms, gluing their surfaces along the
common collar, and is not proved here.

## Main definitions

* `TauCeti.KnotCobordism K₀ K₁`: a smooth knot cobordism from `K₀` to `K₁`, in collared form.
* `TauCeti.KnotCobordism.genus`: the genus `⌊dim H₁(S; ℚ) / 2⌋` of a knot cobordism.
* `TauCeti.KnotCobordism.ofConcordance`: the cobordism traced by a concordance.
* `TauCeti.KnotCobordism.symm`: the reverse of a knot cobordism, with heights reflected.
* `TauCeti.KnotCobordism.transDiffeomorph`: the transport of a knot cobordism along an ambient
  diffeomorphism.
* `TauCeti.KnotCobordism.transConcordance`,
  `TauCeti.SmoothEmbedding.Concordance.transKnotCobordism`: a knot cobordism followed by a
  concordance, and a concordance followed by a knot cobordism, on the same surface.
* `TauCeti.cobordismDistance K₀ K₁`: the least genus of a knot cobordism from `K₀` to `K₁`, in
  `ℕ∞`.

## Main results

* `TauCeti.KnotCobordism.genus_ofConcordance`: a concordance is a cobordism of genus `0`.
* `TauCeti.cobordismDistance_le_genus`, `TauCeti.le_cobordismDistance_iff`,
  `TauCeti.cobordismDistance_lt_top_iff`, `TauCeti.exists_genus_eq_cobordismDistance`: the
  cobordism distance is the infimum of the genera of the cobordisms, attained when finite.
* `TauCeti.cobordismDistance_congr_range`: the cobordism distance only depends on the images of the
  knots.
* `TauCeti.SmoothEmbedding.Concordant.cobordismDistance_eq_zero`, `TauCeti.cobordismDistance_self`:
  concordant knots, and in particular a knot and itself, are at cobordism distance `0`.
* `TauCeti.cobordismDistance_comm`: the cobordism distance is symmetric.
* `TauCeti.cobordismDistance_reverse_left`, `TauCeti.cobordismDistance_rotate_left` and their
  `_right` forms: the cobordism distance does not depend on the orientations or the base points of
  the parametrizations of the knots.
* `TauCeti.cobordismDistance_transDiffeomorph`: the cobordism distance is invariant under
  diffeomorphisms of the ambient spheres.
* `TauCeti.KnotCobordism.genus_transConcordance`,
  `TauCeti.SmoothEmbedding.Concordance.genus_transKnotCobordism`: composing with a concordance keeps
  the genus.
* `TauCeti.KnotCobordism.exists_range_toFun_transConcordance`,
  `TauCeti.SmoothEmbedding.Concordance.exists_range_toFun_transKnotCobordism`: the embedded surface
  of the composite is that of the cobordism away from a collar, and the rescaled annulus of the
  concordance on it.
* `TauCeti.cobordismDistance_congr_concordant`: the cobordism distance is a concordance invariant
  in each argument.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for knot cobordisms in `S³ × [0, 1]` and the four-ball genus.
* S. Baader, *Scissor equivalence for torus links*, Bull. Lond. Math. Soc. 44 (2012), 1068–1078,
  for the cobordism distance of knots.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Manifold Metric Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A smooth **knot cobordism** from the knot `K₀` to the knot `K₁` in the unit sphere `Sⁿ` of `E`,
in collared form: a connected, orientable smooth surface, modelled on `ℝ¹ × ℝ`, with a smooth
embedding into `Sⁿ × ℝ` which is proper over the slab `Sⁿ × [0, 1]` and whose image is the
cylinder over `K₀` at heights at most `ε` and the cylinder over `K₁` at heights at least `1 - ε`,
for some `ε > 0`. -/
structure KnotCobordism (K₀ K₁ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) where
  /-- The underlying surface. -/
  carrier : Type
  /-- The topology of the surface. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- The charts of the surface, modelled on `ℝ¹ × ℝ`. -/
  [chartedSpace : ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) ℝ) carrier]
  /-- The surface is a smooth manifold. -/
  [isManifold : IsManifold ((𝓡 1).prod 𝓘(ℝ)) ∞ carrier]
  /-- The surface is connected. -/
  [connectedSpace : ConnectedSpace carrier]
  /-- The surface is orientable. -/
  [orientable : Orientable ((𝓡 1).prod 𝓘(ℝ)) carrier]
  /-- The embedding of the surface into `Sⁿ × ℝ`. -/
  toFun : carrier → sphere (0 : E) 1 × ℝ
  /-- The surface is smoothly embedded. -/
  isSmoothEmbedding : IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ toFun
  /-- The part of the surface over the slab `Sⁿ × [0, 1]` is compact. -/
  isCompact_preimage_Icc : IsCompact {x | (toFun x).2 ∈ Icc (0 : ℝ) 1}
  /-- Near height `0` the surface is the cylinder over `K₀`. -/
  exists_pos_range_inter_snd_le :
    ∃ ε > 0, range toFun ∩ {p | p.2 ≤ ε} = range K₀ ×ˢ Iic ε
  /-- Near height `1` the surface is the cylinder over `K₁`. -/
  exists_pos_range_inter_le_snd :
    ∃ ε > 0, range toFun ∩ {p | 1 - ε ≤ p.2} = range K₁ ×ˢ Ici (1 - ε)

namespace KnotCobordism

attribute [instance] topologicalSpace chartedSpace isManifold connectedSpace orientable

variable {K₀ K₁ K₀' K₁' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The first singular homology `H₁(S; ℚ)` of a knot cobordism, with rational coefficients. -/
abbrev firstHomology (S : KnotCobordism K₀ K₁) : Type :=
  ((singularHomologyFunctor (ModuleCat ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj (TopCat.of S.carrier)

/-- The **genus** of a knot cobordism: `⌊dim H₁(S; ℚ) / 2⌋`. A compact, connected, orientable
surface of genus `g` with two boundary circles has `H₁ ≅ ℚ²ᵍ⁺¹`, and the collared surface `S`
deformation retracts onto such a surface, its part over the slab. -/
def genus (S : KnotCobordism K₀ K₁) : ℕ :=
  finrank ℚ S.firstHomology / 2

/-- The genus of a knot cobordism is half the dimension of its first rational homology, rounded
down. -/
theorem genus_def (S : KnotCobordism K₀ K₁) : S.genus = finrank ℚ S.firstHomology / 2 :=
  (rfl)

/-- A knot cobordism from `K₀` to `K₁` is one between any knots with the same images. -/
def congrRange (S : KnotCobordism K₀ K₁) (h₀ : range K₀ = range K₀')
    (h₁ : range K₁ = range K₁') : KnotCobordism K₀' K₁' where
  carrier := S.carrier
  toFun := S.toFun
  isSmoothEmbedding := S.isSmoothEmbedding
  isCompact_preimage_Icc := S.isCompact_preimage_Icc
  exists_pos_range_inter_snd_le := h₀ ▸ S.exists_pos_range_inter_snd_le
  exists_pos_range_inter_le_snd := h₁ ▸ S.exists_pos_range_inter_le_snd

/-- Transporting a knot cobordism to knots with the same images keeps its genus. -/
@[simp]
theorem genus_congrRange (S : KnotCobordism K₀ K₁) (h₀ : range K₀ = range K₀')
    (h₁ : range K₁ = range K₁') : (S.congrRange h₀ h₁).genus = S.genus :=
  (rfl)

/-- Transporting a knot cobordism to knots with the same images keeps its surface. -/
theorem carrier_congrRange (S : KnotCobordism K₀ K₁) (h₀ : range K₀ = range K₀')
    (h₁ : range K₁ = range K₁') : (S.congrRange h₀ h₁).carrier = S.carrier :=
  (rfl)

/-- Transporting a knot cobordism to knots with the same images keeps its embedded surface. -/
@[simp]
theorem range_toFun_congrRange (S : KnotCobordism K₀ K₁) (h₀ : range K₀ = range K₀')
    (h₁ : range K₁ = range K₁') : range (S.congrRange h₀ h₁).toFun = range S.toFun :=
  (rfl)

/-- The **cobordism traced by a concordance**: the track `S¹ × ℝ → Sⁿ × ℝ` of a smooth concordance
from `K₀` to `K₁` is a knot cobordism, its surface the cylinder `S¹ × ℝ`. -/
def ofConcordance (F : SmoothEmbedding.Concordance K₀ K₁) : KnotCobordism K₀ K₁ where
  carrier := Circle × ℝ
  toFun := F
  isSmoothEmbedding := F.toSmoothEmbedding.isSmoothEmbedding
  isCompact_preimage_Icc := by
    have h : {p : Circle × ℝ | (F p).2 ∈ Icc (0 : ℝ) 1} = univ ×ˢ Icc 0 1 := by
      ext ⟨x, t⟩
      simpa using F.isCollaredTrack.snd_apply_mem_Icc_iff x (t := t)
    rw [h]
    exact isCompact_univ.prod isCompact_Icc
  exists_pos_range_inter_snd_le :=
    F.isCollaredTrack.exists_pos_range_inter_snd_le F.toSmoothEmbedding.isEmbedding.continuous
  exists_pos_range_inter_le_snd :=
    F.isCollaredTrack.exists_pos_range_inter_le_snd F.toSmoothEmbedding.isEmbedding.continuous

/-- The surface of the cobordism traced by a concordance is the cylinder `S¹ × ℝ`. -/
theorem carrier_ofConcordance (F : SmoothEmbedding.Concordance K₀ K₁) :
    (ofConcordance F).carrier = (Circle × ℝ) :=
  (rfl)

/-- The embedded surface of the cobordism traced by a concordance is the image of its track. -/
@[simp]
theorem range_toFun_ofConcordance (F : SmoothEmbedding.Concordance K₀ K₁) :
    range (ofConcordance F).toFun = range F :=
  (rfl)

/-- **A concordance is a cobordism of genus `0`**: the first homology of the cylinder `S¹ × ℝ` is
one copy of `ℚ`. -/
@[simp]
theorem genus_ofConcordance (F : SmoothEmbedding.Concordance K₀ K₁) :
    (ofConcordance F).genus = 0 := by
  -- The cylinder `S¹ × ℝ` is homotopy equivalent to the one-circle torus `Unit → S¹`.
  let e := ContinuousMap.HomotopyEquiv.prodContractible Circle ℝ
  have h := ((e.trans (Homeomorph.ulift.symm.trans
      (Homeomorph.funUnique Unit (ULift.{0} Circle)).symm).toHomotopyEquiv).singularHomologyIso
    (ModuleCat.of ℚ ℚ) 1).toLinearEquiv.finrank_eq
  rw [finrank_singularHomology_pi_circle] at h
  simp only [Nat.card_unique, Nat.choose_self, finrank_self, mul_one] at h
  -- The first homology of the cobordism is, by definition, that of the cylinder `S¹ × ℝ`.
  rw [genus_def]
  exact (congrArg (· / 2) h).trans (by norm_num)

/-! ### Reversal and ambient transport -/

/-- The **reverse** of a knot cobordism from `K₀` to `K₁`: the same surface, with its heights
reflected by `t ↦ 1 - t`, is a knot cobordism from `K₁` to `K₀`. -/
def symm (S : KnotCobordism K₀ K₁) : KnotCobordism K₁ K₀ where
  carrier := S.carrier
  toFun x := ((S.toFun x).1, 1 - (S.toFun x).2)
  isSmoothEmbedding := by
    convert isSmoothEmbedding_diffeomorph_comp S.isSmoothEmbedding
      ((Diffeomorph.refl (𝓡 n) (sphere (0 : E) 1) ∞).prodCongr (Diffeomorph.subLeft ℝ ∞ 1))
      using 1
    ext x <;> simp [Diffeomorph.coe_prodCongr]
  isCompact_preimage_Icc := by
    have h : {x | ((S.toFun x).1, 1 - (S.toFun x).2).2 ∈ Icc (0 : ℝ) 1} =
        {x | (S.toFun x).2 ∈ Icc (0 : ℝ) 1} := by
      ext x
      simp only [mem_ofPred_eq, mem_Icc, sub_nonneg, sub_le_self_iff]
      exact and_comm
    rw [h]
    exact S.isCompact_preimage_Icc
  exists_pos_range_inter_snd_le := by
    obtain ⟨ε, hε, h⟩ := S.exists_pos_range_inter_le_snd
    refine ⟨ε, hε, Set.ext fun p ↦ ?_⟩
    have hp := Set.ext_iff.1 h (p.1, 1 - p.2)
    have e (x : S.carrier) : 1 - (S.toFun x).2 = p.2 ↔ (S.toFun x).2 = 1 - p.2 := by
      constructor <;> intro <;> linarith
    simp only [mem_inter_iff, mem_range, mem_ofPred_eq, mem_prod, mem_Ici, mem_Iic,
      sub_le_sub_iff_left, Prod.ext_iff, e] at hp ⊢
    exact hp
  exists_pos_range_inter_le_snd := by
    obtain ⟨ε, hε, h⟩ := S.exists_pos_range_inter_snd_le
    refine ⟨ε, hε, Set.ext fun p ↦ ?_⟩
    have hp := Set.ext_iff.1 h (p.1, 1 - p.2)
    have e (x : S.carrier) : 1 - (S.toFun x).2 = p.2 ↔ (S.toFun x).2 = 1 - p.2 := by
      constructor <;> intro <;> linarith
    have e' : 1 - ε ≤ p.2 ↔ 1 - p.2 ≤ ε := sub_le_comm
    simp only [mem_inter_iff, mem_range, mem_ofPred_eq, mem_prod, mem_Ici, mem_Iic, Prod.ext_iff,
      e, e'] at hp ⊢
    exact hp

/-- The reverse of a knot cobordism has the same surface. -/
theorem carrier_symm (S : KnotCobordism K₀ K₁) : S.symm.carrier = S.carrier :=
  (rfl)

/-- The embedded surface of the reverse of a knot cobordism is its reflection in the level
`1 / 2`. -/
@[simp]
theorem range_toFun_symm (S : KnotCobordism K₀ K₁) :
    range S.symm.toFun = (fun p : sphere (0 : E) 1 × ℝ ↦ (p.1, 1 - p.2)) '' range S.toFun := by
  rw [← range_comp]
  rfl

/-- Reversing a knot cobordism keeps its genus. -/
@[simp]
theorem genus_symm (S : KnotCobordism K₀ K₁) : S.symm.genus = S.genus :=
  (rfl)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]

/-- Transport of a knot cobordism along a diffeomorphism `Ψ : Sⁿ ≃ₘ Sⁿ` of the ambient spheres: the
same surface, embedded by `Ψ × id`, is a knot cobordism between the transported knots. -/
def transDiffeomorph (S : KnotCobordism K₀ K₁)
    (Ψ : sphere (0 : E) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1) :
    KnotCobordism (K₀.transDiffeomorph Ψ) (K₁.transDiffeomorph Ψ) where
  carrier := S.carrier
  toFun x := (Ψ (S.toFun x).1, (S.toFun x).2)
  isSmoothEmbedding := isSmoothEmbedding_diffeomorph_comp S.isSmoothEmbedding
    (Ψ.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞))
  isCompact_preimage_Icc := S.isCompact_preimage_Icc
  exists_pos_range_inter_snd_le := by
    obtain ⟨ε, hε, h⟩ := S.exists_pos_range_inter_snd_le
    refine ⟨ε, hε, Set.ext fun p ↦ ?_⟩
    have hp := Set.ext_iff.1 h (Ψ.symm p.1, p.2)
    have e (y) : Ψ y = p.1 ↔ y = Ψ.symm p.1 :=
      ⟨fun h ↦ h ▸ (Ψ.symm_apply_apply y).symm, fun h ↦ h ▸ Ψ.apply_symm_apply p.1⟩
    simp only [mem_inter_iff, mem_range, mem_ofPred_eq, mem_prod, mem_Iic, Prod.ext_iff,
      SmoothEmbedding.coe_transDiffeomorph, Function.comp_apply, e] at hp ⊢
    exact hp
  exists_pos_range_inter_le_snd := by
    obtain ⟨ε, hε, h⟩ := S.exists_pos_range_inter_le_snd
    refine ⟨ε, hε, Set.ext fun p ↦ ?_⟩
    have hp := Set.ext_iff.1 h (Ψ.symm p.1, p.2)
    have e (y) : Ψ y = p.1 ↔ y = Ψ.symm p.1 :=
      ⟨fun h ↦ h ▸ (Ψ.symm_apply_apply y).symm, fun h ↦ h ▸ Ψ.apply_symm_apply p.1⟩
    simp only [mem_inter_iff, mem_range, mem_ofPred_eq, mem_prod, mem_Ici, Prod.ext_iff,
      SmoothEmbedding.coe_transDiffeomorph, Function.comp_apply, e] at hp ⊢
    exact hp

/-- Transporting a knot cobordism along an ambient diffeomorphism keeps its surface. -/
theorem carrier_transDiffeomorph (S : KnotCobordism K₀ K₁)
    (Ψ : sphere (0 : E) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1) :
    (S.transDiffeomorph Ψ).carrier = S.carrier :=
  (rfl)

/-- Transporting a knot cobordism along an ambient diffeomorphism `Ψ` moves its embedded surface by
`Ψ × id`. -/
@[simp]
theorem range_toFun_transDiffeomorph (S : KnotCobordism K₀ K₁)
    (Ψ : sphere (0 : E) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1) :
    range (S.transDiffeomorph Ψ).toFun = Prod.map Ψ id '' range S.toFun := by
  rw [← range_comp]
  rfl

/-- Transporting a knot cobordism along an ambient diffeomorphism keeps its genus. -/
@[simp]
theorem genus_transDiffeomorph (S : KnotCobordism K₀ K₁)
    (Ψ : sphere (0 : E) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1) :
    (S.transDiffeomorph Ψ).genus = S.genus :=
  (rfl)

/-! ### Composing with a concordance -/

section Concordance

open Filter Topology

variable {K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  (C : SmoothEmbedding.Concordance K₁ K₂) {c : ℝ}

/-- The concordance `C` run during the time interval `[1 - c, 1]`, conjugated by the affine change
of time `t ↦ (t - (1 - c)) / c`. -/
private def rescale (hc : 0 < c) :
    SmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (Circle × ℝ) (sphere (0 : E) 1 × ℝ) :=
  C.toSmoothEmbedding.conjTime c⁻¹ (-((1 - c) / c)) (inv_ne_zero hc.ne')

private theorem rescale_apply (hc : 0 < c) (z : Circle) (t : ℝ) :
    rescale C hc (z, t) = ((C (z, (t - (1 - c)) / c)).1,
      1 - c + c * (C (z, (t - (1 - c)) / c)).2) := by
  have ht : c⁻¹ * t + -((1 - c) / c) = (t - (1 - c)) / c := by field_simp; ring
  rw [rescale, SmoothEmbedding.coe_conjTime, conjTime_apply, ht,
    SmoothEmbedding.Concordance.coe_toSmoothEmbedding]
  refine Prod.ext rfl ?_
  field_simp
  ring

/-- Until time `1 - c` the rescaled concordance is the cylinder over its initial knot. -/
private theorem rescale_apply_of_le (hc : 0 < c) (z : Circle) {t : ℝ} (ht : t ≤ 1 - c) :
    rescale C hc (z, t) = (K₁ z, t) := by
  rw [rescale_apply, C.isCollaredTrack.apply_of_nonpos z
    (div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le)]
  refine Prod.ext rfl ?_
  field_simp
  ring

/-- From time `1` on the rescaled concordance is the cylinder over its final knot. -/
private theorem rescale_apply_of_one_le (hc : 0 < c) (z : Circle) {t : ℝ} (ht : 1 ≤ t) :
    rescale C hc (z, t) = (K₂ z, t) := by
  rw [rescale_apply, C.isCollaredTrack.apply_of_one_le z ((le_div_iff₀ hc).2 (by linarith))]
  refine Prod.ext rfl ?_
  field_simp
  ring

/-- The rescaled concordance keeps the heights above `1 - c` above `1 - c`, and those below it
below it. -/
private theorem lt_snd_rescale_iff (hc : 0 < c) (z : Circle) (t : ℝ) :
    1 - c < (rescale C hc (z, t)).2 ↔ 1 - c < t := by
  have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h ↦ lt_irrefl _ h.1
  rw [rescale_apply, lt_add_iff_pos_right, mul_pos_iff_of_pos_left hc,
    C.isCollaredTrack.lt_snd_apply_iff z h0, div_pos_iff_of_pos_right hc, sub_pos]

/-- The parameters `(z, t)` of a point `x` of a knot cobordism from `K₀` to `K₁` lying on the
cylinder over `K₁`, for which `S x = (K₁ z, t)`. -/
private def collarParam (S : KnotCobordism K₀ K₁) (x : S.carrier) : Circle × ℝ :=
  (Function.invFun K₁ (S.toFun x).1, (S.toFun x).2)

/-- From height `a` on, the embedded surface of `S` is the cylinder over `K₁`. -/
private def IsCylinderFrom (S : KnotCobordism K₀ K₁) (a : ℝ) : Prop :=
  ∀ p : sphere (0 : E) 1 × ℝ, a ≤ p.2 → (p ∈ range S.toFun ↔ p.1 ∈ range K₁)

variable {S : KnotCobordism K₀ K₁}

private theorem prodMap_collarParam {x : S.carrier} (hx : (S.toFun x).1 ∈ range K₁) :
    Prod.map K₁ id (collarParam S x) = S.toFun x :=
  Prod.ext (Function.invFun_eq hx) rfl

private theorem fst_mem_range_of_le
    (hS : IsCylinderFrom S (1 - 2 * c)) {x : S.carrier}
    (hx : 1 - 2 * c ≤ (S.toFun x).2) : (S.toFun x).1 ∈ range K₁ :=
  (hS (S.toFun x) hx).1 (mem_range_self x)

variable (S) in
/-- The points of the surface of `S` lying above a given height form an open set. -/
private theorem isOpen_lt_snd_toFun (a : ℝ) : IsOpen {y : S.carrier | a < (S.toFun y).2} :=
  isOpen_lt continuous_const (continuous_snd.comp S.isSmoothEmbedding.isEmbedding.continuous)

/-- Near a point of `S` above height `1 - 2 c`, `S` is recovered from the parameters of its
points. -/
private theorem eventuallyEq_prodMap_collarParam
    (hS : IsCylinderFrom S (1 - 2 * c)) {x : S.carrier}
    (hx : 1 - 2 * c < (S.toFun x).2) :
    Prod.map K₁ id ∘ collarParam S =ᶠ[𝓝 x] S.toFun :=
  eventuallyEq_of_mem ((isOpen_lt_snd_toFun S _).mem_nhds hx) fun _ hy ↦
    prodMap_collarParam (fst_mem_range_of_le hS (le_of_lt hy))

/-- On the cylinder over `K₁`, the parameters of a point depend smoothly on it: the point is
`K₁ z` in its first coordinate, and `K₁` is an immersion and a topological embedding. -/
private theorem contMDiffAt_collarParam
    (hS : IsCylinderFrom S (1 - 2 * c)) {x : S.carrier}
    (hx : 1 - 2 * c < (S.toFun x).2) :
    ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) ∞ (collarParam S) x := by
  have hΦ := S.isSmoothEmbedding.isImmersion.contMDiff
  have hev : (K₁ ∘ fun y ↦ Function.invFun K₁ (S.toFun y).1) =ᶠ[𝓝 x] fun y ↦ (S.toFun y).1 :=
    (eventuallyEq_prodMap_collarParam hS hx).fun_comp Prod.fst
  have hz : ContMDiffAt ((𝓡 1).prod 𝓘(ℝ)) (𝓡 1) ∞
      (fun y ↦ Function.invFun K₁ (S.toFun y).1) x := by
    refine (ContMDiffAt.iff_comp_isImmersionAt (K₁.isImmersion.isImmersionAt _)).2 ⟨?_, ?_⟩
    · exact K₁.isEmbedding.isInducing.continuousAt_iff.2
        ((continuous_fst.comp hΦ.continuous).continuousAt.congr hev.symm)
    · exact (contMDiff_fst.comp hΦ).contMDiffAt.congr_of_eventuallyEq hev
  exact hz.prodMk (contMDiff_snd.comp hΦ).contMDiffAt

/-- On the cylinder over `K₁`, the manifold derivative of the parameters is injective, since
composing it with the derivative of `K₁ × id` gives that of the embedding of the surface. -/
private theorem injective_mfderiv_collarParam
    (hS : IsCylinderFrom S (1 - 2 * c)) {x : S.carrier}
    (hx : 1 - 2 * c < (S.toFun x).2) :
    Function.Injective (mfderiv ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 1).prod 𝓘(ℝ)) (collarParam S) x) := by
  have hev := eventuallyEq_prodMap_collarParam hS hx
  have hK : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (Prod.map K₁ (id : ℝ → ℝ)) :=
    K₁.contMDiff.prodMap contMDiff_id
  have h := ((S.isSmoothEmbedding.isImmersion.isImmersionAt x).congr_of_eventuallyEq
    hev.symm).mfderiv_injective (by simp)
  rw [mfderiv_comp x (hK.contMDiffAt.mdifferentiableAt (by simp))
    ((contMDiffAt_collarParam hS hx).mdifferentiableAt (by simp)),
    ContinuousLinearMap.coe_comp] at h
  exact h.of_comp

/-- The embedding of the composite of `S` and `C`: below height `1 - c` it is that of `S`, and on
the cylinder over `K₁` above it, `S`'s cylinder is replaced by the concordance `C`, rescaled to run
during the time interval `[1 - c, 1]`. -/
private def glueFun (S : KnotCobordism K₀ K₁) (hc : 0 < c) (x : S.carrier) :
    sphere (0 : E) 1 × ℝ :=
  if (S.toFun x).2 ≤ 1 - c then S.toFun x else rescale C hc (collarParam S x)

private theorem glueFun_of_le (hc : 0 < c) {x : S.carrier} (hx : (S.toFun x).2 ≤ 1 - c) :
    glueFun C S hc x = S.toFun x := by
  simp only [glueFun, hx, ↓reduceIte]

private theorem glueFun_of_le_snd (hc : 0 < c)
    (hS : IsCylinderFrom S (1 - 2 * c)) {x : S.carrier}
    (hx : 1 - 2 * c ≤ (S.toFun x).2) : glueFun C S hc x = rescale C hc (collarParam S x) := by
  rw [glueFun]
  split_ifs with h
  · rw [← prodMap_collarParam (fst_mem_range_of_le hS hx), Prod.map_apply, id_eq]
    exact (rescale_apply_of_le C hc (collarParam S x).1 (t := (collarParam S x).2) h).symm
  · rfl

/-- On the cylinder over `K₁` above height `1 - 2 c`, the glued map is the rescaled
concordance. -/
private theorem glueFun_of_eq (hc : 0 < c)
    (hS : IsCylinderFrom S (1 - 2 * c)) {x : S.carrier} {z : Circle} {t : ℝ}
    (hx : S.toFun x = (K₁ z, t)) (ht : 1 - 2 * c ≤ t) :
    glueFun C S hc x =
      ((C (z, (t - (1 - c)) / c)).1, 1 - c + c * (C (z, (t - (1 - c)) / c)).2) := by
  have hcp : collarParam S x = (z, t) := by
    rw [collarParam, hx]
    exact Prod.ext (Function.leftInverse_invFun K₁.isEmbedding.injective z) rfl
  rw [glueFun_of_le_snd C hc hS (by rw [hx]; exact ht), hcp, rescale_apply]

/-- The rescaled annulus of `C` over the times `s > 0` lies on the glued surface. -/
private theorem mem_range_glueFun_of_pos (hc : 0 < c)
    (hS : IsCylinderFrom S (1 - 2 * c)) (z : Circle) {s : ℝ} (hs : 0 < s) :
    ((C (z, s)).1, 1 - c + c * (C (z, s)).2) ∈ range (glueFun C S hc) := by
  obtain ⟨x, hx⟩ := (hS (K₁ z, 1 - c + c * s) (by dsimp only; nlinarith)).2 (mem_range_self z)
  have ht : (1 - c + c * s - (1 - c)) / c = s := by field_simp; ring
  exact ⟨x, by rw [glueFun_of_eq C hc hS hx (by nlinarith), ht]⟩

/-- Gluing in the concordance keeps the heights above `1 - c` above `1 - c`, and those below it
below it. -/
private theorem lt_snd_glueFun_iff (hc : 0 < c)
    (hS : IsCylinderFrom S (1 - 2 * c)) (x : S.carrier) :
    1 - c < (glueFun C S hc x).2 ↔ 1 - c < (S.toFun x).2 := by
  by_cases hx : (S.toFun x).2 ≤ 1 - c
  · rw [glueFun_of_le C hc hx]
  · rw [glueFun_of_le_snd C hc hS (by linarith), collarParam, lt_snd_rescale_iff]

private theorem isImmersionAt_glueFun (hc : 0 < c)
    (hS : IsCylinderFrom S (1 - 2 * c)) (x : S.carrier) :
    IsImmersionAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (glueFun C S hc) x := by
  have hΦ := S.isSmoothEmbedding.isImmersion
  have hcont : Continuous fun y ↦ (S.toFun y).2 := continuous_snd.comp hΦ.contMDiff.continuous
  rcases lt_or_ge (S.toFun x).2 (1 - c) with hx | hx
  · exact (hΦ.isImmersionAt x).congr_of_eventuallyEq <| eventuallyEq_of_mem
      ((isOpen_lt hcont continuous_const).mem_nhds hx) fun y hy ↦ (glueFun_of_le C hc hy.le).symm
  have hx' : 1 - 2 * c < (S.toFun x).2 := by linarith
  have hU := isOpen_lt_snd_toFun S (1 - 2 * c)
  have hsm : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞
      (rescale C hc ∘ collarParam S) {y | 1 - 2 * c < (S.toFun y).2} := fun y hy ↦
    ((rescale C hc).contMDiff.contMDiffAt.comp y (contMDiffAt_collarParam hS hy)).contMDiffWithinAt
  have himm : IsImmersionAt ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞
      (rescale C hc ∘ collarParam S) x := by
    rw [hsm.isImmersionAt_iff_injective_mfderiv hU hx' (by simp),
      mfderiv_comp x ((rescale C hc).contMDiff.contMDiffAt.mdifferentiableAt (by simp))
        ((contMDiffAt_collarParam hS hx').mdifferentiableAt (by simp)),
      ContinuousLinearMap.coe_comp]
    exact ((rescale C hc).isImmersion.mfderiv_injective (by simp) _).comp
      (injective_mfderiv_collarParam hS hx')
  exact himm.congr_of_eventuallyEq <| eventuallyEq_of_mem (hU.mem_nhds hx') fun y hy ↦
    (glueFun_of_le_snd C hc hS hy.le).symm

/-- The glued map is a topological embedding: the open slabs below height `1 - c` and above height
`1 - 2 c` cover `Sⁿ × ℝ`, and over them it is the embedding of `S`, respectively the rescaled
concordance composed with the parameters of the cylinder over `K₁`. -/
private theorem isEmbedding_glueFun (hc : 0 < c)
    (hS : IsCylinderFrom S (1 - 2 * c)) :
    IsEmbedding (glueFun C S hc) := by
  have hΦ := S.isSmoothEmbedding
  have hglue : Continuous (glueFun C S hc) := continuous_iff_continuousAt.2 fun x ↦
    (isImmersionAt_glueFun C hc hS x).continuousAt
  let U : Bool → TopologicalSpace.Opens (sphere (0 : E) 1 × ℝ) := fun b ↦ bif b
    then ⟨{q | 1 - 2 * c < q.2}, isOpen_lt continuous_const continuous_snd⟩
    else ⟨{q | q.2 < 1 - c}, isOpen_lt continuous_snd continuous_const⟩
  let W : Bool → Set S.carrier := fun b ↦ bif b
    then {y | 1 - 2 * c < (S.toFun y).2} else {y | (S.toFun y).2 < 1 - c}
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range (glueFun C S hc) hglue U ?_
    (fun b ↦ W b) (fun b ↦ Subtype.val) (fun b ↦ continuous_subtype_val) ?_ ?_
  -- The two slabs cover the image.
  · rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    rcases lt_or_ge (glueFun C S hc y).2 (1 - c) with hy | hy
    · exact ⟨false, hy⟩
    · exact ⟨true, (by linarith : 1 - 2 * c < (glueFun C S hc y).2)⟩
  -- A point mapped into a slab lies in the matching slab of the surface.
  · rintro (_ | _) y hy
    · have hle : (S.toFun y).2 ≤ 1 - c :=
        not_lt.1 fun h ↦ (not_lt.2 (le_of_lt hy)) ((lt_snd_glueFun_iff C hc hS y).2 h)
      refine ⟨⟨y, ?_⟩, rfl⟩
      have hy' : (glueFun C S hc y).2 < 1 - c := hy
      rwa [glueFun_of_le C hc hle] at hy'
    · have hy' : 1 - 2 * c < (glueFun C S hc y).2 := hy
      have hlt : 1 - 2 * c < (S.toFun y).2 := by
        by_cases hle : (S.toFun y).2 ≤ 1 - c
        · rwa [glueFun_of_le C hc hle] at hy'
        · linarith
      exact ⟨⟨y, hlt⟩, rfl⟩
  -- On each slab of the surface the glued map is an embedding.
  · rintro (_ | _)
    · have heq : glueFun C S hc ∘ (Subtype.val : W false → S.carrier) =
          S.toFun ∘ Subtype.val :=
        funext fun y ↦ glueFun_of_le C hc (le_of_lt y.2)
      rw [heq]
      exact hΦ.isEmbedding.comp IsEmbedding.subtypeVal
    · have heq : glueFun C S hc ∘ (Subtype.val : W true → S.carrier) =
          rescale C hc ∘ (collarParam S ∘ Subtype.val) :=
        funext fun y ↦ glueFun_of_le_snd C hc hS (le_of_lt y.2)
      have hP : Continuous (collarParam S ∘ (Subtype.val : W true → S.carrier)) :=
        continuous_iff_continuousAt.2 fun y ↦
          (contMDiffAt_collarParam hS y.2).continuousAt.comp continuous_subtype_val.continuousAt
      have hK : Continuous (Prod.map K₁ (id : ℝ → ℝ)) :=
        K₁.isEmbedding.continuous.prodMap continuous_id
      have hPK : Prod.map K₁ id ∘ (collarParam S ∘ (Subtype.val : W true → S.carrier)) =
          S.toFun ∘ Subtype.val :=
        funext fun y ↦ prodMap_collarParam (fst_mem_range_of_le hS (le_of_lt y.2))
      rw [heq]
      refine (rescale C hc).isEmbedding.comp (IsEmbedding.of_comp hP hK ?_)
      rw [hPK]
      exact hΦ.isEmbedding.comp IsEmbedding.subtypeVal

/-- The composite of `S` and `C` for a width `c ∈ (0, 1/2]` such that the top of `S` is the
cylinder over `K₁` from height `1 - 2 c` on. -/
private def transConcordanceOfWidth (hc : 0 < c) (hc₂ : c ≤ 1 / 2)
    (hS : IsCylinderFrom S (1 - 2 * c)) :
    KnotCobordism K₀ K₂ where
  carrier := S.carrier
  toFun := glueFun C S hc
  isSmoothEmbedding := ⟨isImmersion_iff_forall_isImmersionAt.2 (isImmersionAt_glueFun C hc hS),
    isEmbedding_glueFun C hc hS⟩
  isCompact_preimage_Icc := by
    -- Gluing in `C` only moves the points of `S` above height `1 - c`, and keeps those above
    -- height `1` fixed, so a point of the new surface over `[0, 1]` lies over `[0, 1]` in `S`.
    refine S.isCompact_preimage_Icc.of_isClosed_subset (isClosed_Icc.preimage
      (continuous_snd.comp (isEmbedding_glueFun C hc hS).continuous)) fun x hx ↦ ?_
    by_cases hle : (S.toFun x).2 ≤ 1 - c
    · have hx' : (glueFun C S hc x).2 ∈ Icc (0 : ℝ) 1 := hx
      rw [glueFun_of_le C hc hle] at hx'
      exact hx'
    · refine ⟨by linarith, le_of_not_gt fun h₁ ↦ ?_⟩
      have hx' : (glueFun C S hc x).2 ≤ 1 := hx.2
      rw [glueFun_of_le_snd C hc hS (by linarith), collarParam,
        rescale_apply_of_one_le C hc _ h₁.le] at hx'
      exact not_le.2 h₁ hx'
  exists_pos_range_inter_snd_le := by
    -- Below height `1 / 2 ≤ 1 - c` the new surface is that of `S`.
    obtain ⟨ε, hε, h⟩ := S.exists_pos_range_inter_snd_le
    refine ⟨min ε (1 / 2), lt_min hε (by norm_num), Set.ext fun p ↦ ?_⟩
    have hp := Set.ext_iff.1 h p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Iic] at hp ⊢
    constructor
    · rintro ⟨⟨x, rfl⟩, hle⟩
      have hx : (S.toFun x).2 ≤ 1 - c := not_lt.1 fun h' ↦ by
        linarith [(lt_snd_glueFun_iff C hc hS x).2 h', min_le_right ε (1 / 2)]
      rw [glueFun_of_le C hc hx] at hle hp ⊢
      exact ⟨(hp.1 ⟨mem_range_self x, hle.trans (min_le_left _ _)⟩).1, hle⟩
    · rintro ⟨hK, hle⟩
      obtain ⟨x, hx⟩ := (hp.2 ⟨hK, hle.trans (min_le_left _ _)⟩).1
      refine ⟨⟨x, ?_⟩, hle⟩
      rw [glueFun_of_le C hc (by rw [hx]; linarith [min_le_right ε (1 / 2)]), hx]
  exists_pos_range_inter_le_snd := by
    -- Above height `1 - c δ` the new surface is the rescaled final collar of `C`.
    obtain ⟨δ, hδ, h⟩ :=
      C.isCollaredTrack.exists_pos_range_inter_le_snd C.toSmoothEmbedding.isEmbedding.continuous
    have hδ₀ : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
    have hδ₁ : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    have hδ₂ : min δ (1 / 2) ≤ δ := min_le_left _ _
    refine ⟨c * min δ (1 / 2), mul_pos hc hδ₀, Set.ext fun p ↦ ?_⟩
    simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ici]
    constructor
    · rintro ⟨⟨x, rfl⟩, hle⟩
      have hx : 1 - c < (S.toFun x).2 :=
        (lt_snd_glueFun_iff C hc hS x).1 (by nlinarith)
      rw [glueFun_of_le_snd C hc hS (by linarith), collarParam, rescale_apply] at hle ⊢
      refine ⟨((Set.ext_iff.1 h _).1 ⟨mem_range_self _, ?_⟩).1, hle⟩
      simp only [mem_ofPred_eq]
      nlinarith
    · rintro ⟨hK, hle⟩
      have hH' : 1 - min δ (1 / 2) ≤ (p.2 - (1 - c)) / c := by
        rw [le_div_iff₀ hc]
        linarith
      have hH : 1 - δ ≤ (p.2 - (1 - c)) / c := by linarith
      obtain ⟨⟨z, s⟩, hzs⟩ := ((Set.ext_iff.1 h (p.1, (p.2 - (1 - c)) / c)).2 ⟨hK, hH⟩).1
      have h0 : (0 : ℝ) ∉ Ioo 0 1 := fun h ↦ lt_irrefl _ h.1
      have hs : 0 < s :=
        (C.isCollaredTrack.lt_snd_apply_iff z h0).1 (by rw [hzs]; dsimp only; linarith)
      obtain ⟨x, hx⟩ := mem_range_glueFun_of_pos C hc hS z hs
      refine ⟨⟨x, ?_⟩, hle⟩
      rw [hx, hzs]
      refine Prod.ext rfl ?_
      field_simp
      ring

variable (S) in
/-- The width of the collar of `S` used to compose it with a concordance. -/
private def width : ℝ :=
  min S.exists_pos_range_inter_le_snd.choose 1 / 2

private theorem width_pos : 0 < width S :=
  half_pos (lt_min S.exists_pos_range_inter_le_snd.choose_spec.1 one_pos)

private theorem width_le : width S ≤ 1 / 2 := by
  have := min_le_right S.exists_pos_range_inter_le_snd.choose 1
  rw [width]
  linarith

/-- From height `1 - 2 * width S` on, `S` is the cylinder over `K₁`. -/
private theorem mem_range_toFun_iff_of_width (p : sphere (0 : E) 1 × ℝ)
    (hp : 1 - 2 * width S ≤ p.2) : p ∈ range S.toFun ↔ p.1 ∈ range K₁ := by
  have hε := S.exists_pos_range_inter_le_snd.choose_spec
  have hε₁ := min_le_left S.exists_pos_range_inter_le_snd.choose 1
  have h := Set.ext_iff.1 hε.2 p
  simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_Ici] at h
  have hp' : 1 - S.exists_pos_range_inter_le_snd.choose ≤ p.2 := by rw [width] at hp; linarith
  exact ⟨fun hr ↦ (h.1 ⟨hr, hp'⟩).1, fun hK ↦ (h.2 ⟨hK, hp'⟩).1⟩

variable (S) in
/-- **Composing a knot cobordism with a concordance**: a knot cobordism `S` from `K₀` to `K₁`
followed by a concordance `C` from `K₁` to `K₂` is a knot cobordism from `K₀` to `K₂` on the same
surface. Up to a height `1 - c` close to `1` the surface is embedded as by `S`; above it, where `S`
is the cylinder over `K₁`, that cylinder is replaced by the annulus of `C`, run during the time
interval `[1 - c, 1]`. -/
def transConcordance : KnotCobordism K₀ K₂ :=
  transConcordanceOfWidth C (width_pos (S := S)) width_le mem_range_toFun_iff_of_width

variable (S) in
/-- The embedding of the composite of `S` and `C` is the gluing of `S` with the rescaled `C`. -/
private theorem toFun_transConcordance :
    (S.transConcordance C).toFun = glueFun C S (width_pos (S := S)) :=
  rfl

variable (S) in
/-- Composing a knot cobordism with a concordance keeps its surface. -/
theorem carrier_transConcordance : (S.transConcordance C).carrier = S.carrier :=
  (rfl)

variable (S) in
/-- Composing a knot cobordism with a concordance keeps its genus. -/
@[simp]
theorem genus_transConcordance : (S.transConcordance C).genus = S.genus :=
  (rfl)

variable (S) in
/-- **The embedded surface of the composite of `S` and `C`**: for some width `c ∈ (0, 1/2]`, it is
the part of the surface of `S` up to height `1 - c`, together with the part of the annulus of `C`
over the times `s > 0`, its heights `h` rescaled to `1 - c + c * h`. -/
theorem exists_range_toFun_transConcordance :
    ∃ c, 0 < c ∧ c ≤ 1 / 2 ∧ range (S.transConcordance C).toFun =
      range S.toFun ∩ {p | p.2 ≤ 1 - c} ∪
        (fun q : Circle × ℝ ↦ ((C q).1, 1 - c + c * (C q).2)) '' (univ ×ˢ Ioi 0) := by
  refine ⟨width S, width_pos, width_le, ?_⟩
  have hc := width_pos (S := S)
  rw [toFun_transConcordance]
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    by_cases hx : (S.toFun x).2 ≤ 1 - width S
    · rw [glueFun_of_le C width_pos hx]
      exact Or.inl ⟨mem_range_self x, hx⟩
    · obtain ⟨z, hz⟩ := fst_mem_range_of_le (S := S) mem_range_toFun_iff_of_width
        (x := x) (by linarith)
      have hS : S.toFun x = (K₁ z, (S.toFun x).2) := Prod.ext hz.symm rfl
      rw [glueFun_of_eq C width_pos mem_range_toFun_iff_of_width hS (by linarith)]
      exact Or.inr ⟨(z, ((S.toFun x).2 - (1 - width S)) / width S),
        ⟨mem_univ _, div_pos (by linarith) hc⟩, rfl⟩
  · rintro (⟨⟨x, rfl⟩, hx⟩ | ⟨⟨z, s⟩, ⟨-, hs⟩, rfl⟩)
    · exact ⟨x, glueFun_of_le C width_pos hx⟩
    · exact mem_range_glueFun_of_pos C width_pos mem_range_toFun_iff_of_width z hs

end Concordance

end KnotCobordism

namespace SmoothEmbedding.Concordance

variable {K₀' K₀ K₁ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- **Composing a concordance with a knot cobordism**: a concordance `C` from `K₀'` to `K₀`
followed by a knot cobordism `S` from `K₀` to `K₁` is a knot cobordism from `K₀'` to `K₁` on the
same surface. It is the reverse of the composite of the reverse of `S` with the reverse of `C`. -/
def transKnotCobordism (C : SmoothEmbedding.Concordance K₀' K₀) (S : KnotCobordism K₀ K₁) :
    KnotCobordism K₀' K₁ :=
  (S.symm.transConcordance C.symm).symm

/-- Composing a concordance with a knot cobordism keeps its surface. -/
theorem carrier_transKnotCobordism (C : SmoothEmbedding.Concordance K₀' K₀)
    (S : KnotCobordism K₀ K₁) : (C.transKnotCobordism S).carrier = S.carrier :=
  (rfl)

/-- Composing a concordance with a knot cobordism keeps its genus. -/
@[simp]
theorem genus_transKnotCobordism (C : SmoothEmbedding.Concordance K₀' K₀)
    (S : KnotCobordism K₀ K₁) : (C.transKnotCobordism S).genus = S.genus :=
  (rfl)

/-- **The embedded surface of the composite of `C` and `S`**: for some width `c ∈ (0, 1/2]`, it is
the part of the surface of `S` from height `c` on, together with the part of the annulus of `C`
over the times `s < 1`, its heights `h` rescaled to `c * h`. -/
theorem exists_range_toFun_transKnotCobordism (C : SmoothEmbedding.Concordance K₀' K₀)
    (S : KnotCobordism K₀ K₁) :
    ∃ c, 0 < c ∧ c ≤ 1 / 2 ∧ range (C.transKnotCobordism S).toFun =
      range S.toFun ∩ {p | c ≤ p.2} ∪
        (fun q : Circle × ℝ ↦ ((C q).1, c * (C q).2)) '' (univ ×ˢ Iio 1) := by
  obtain ⟨c, hc, hc₂, h⟩ := S.symm.exists_range_toFun_transConcordance C.symm
  refine ⟨c, hc, hc₂, ?_⟩
  -- The reflection of the heights is an involution.
  have hrr : Function.LeftInverse (fun p : sphere (0 : E) 1 × ℝ ↦ (p.1, 1 - p.2))
      (fun p ↦ (p.1, 1 - p.2)) := fun p ↦ Prod.ext rfl (sub_sub_cancel _ _)
  have hr (A : Set (sphere (0 : E) 1 × ℝ)) : (fun p ↦ (p.1, 1 - p.2)) '' A =
      (fun p : sphere (0 : E) 1 × ℝ ↦ (p.1, 1 - p.2)) ⁻¹' A :=
    congrFun (image_eq_preimage_of_inverse hrr hrr) A
  rw [transKnotCobordism, KnotCobordism.range_toFun_symm, h, KnotCobordism.range_toFun_symm, hr, hr]
  ext p
  simp only [mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq, sub_sub_cancel,
    sub_le_sub_iff_left]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨⟨z, s⟩, ⟨-, hs⟩, he⟩
    have hs : (0 : ℝ) < s := hs
    dsimp only at he
    rw [symm_apply, Prod.ext_iff] at he
    have hs₁ : 1 - s < 1 := by linarith
    refine ⟨(z, 1 - s), ⟨mem_univ _, hs₁⟩, Prod.ext he.1 ?_⟩
    dsimp only at he ⊢
    linarith [he.2]
  · rintro ⟨⟨z, u⟩, ⟨-, hu⟩, rfl⟩
    have hu : u < 1 := hu
    have hu₀ : (0 : ℝ) < 1 - u := by linarith
    refine ⟨(z, 1 - u), ⟨mem_univ _, hu₀⟩, ?_⟩
    dsimp only
    rw [symm_apply, sub_sub_cancel]
    exact Prod.ext rfl (by dsimp only; ring)

end SmoothEmbedding.Concordance

open KnotCobordism

/-- The **cobordism distance** between the knots `K₀` and `K₁`: the least genus of a knot cobordism
from `K₀` to `K₁`, or `⊤` if there is none. -/
def cobordismDistance (K₀ K₁ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) : ℕ∞ :=
  ⨅ S : KnotCobordism K₀ K₁, (S.genus : ℕ∞)

variable {K₀ K₁ K₀' K₁' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The cobordism distance is the infimum of the genera of all knot cobordisms. -/
theorem cobordismDistance_def :
    cobordismDistance K₀ K₁ = ⨅ S : KnotCobordism K₀ K₁, (S.genus : ℕ∞) :=
  (rfl)

/-- The cobordism distance is at most the genus of any knot cobordism. -/
theorem cobordismDistance_le_genus (S : KnotCobordism K₀ K₁) : cobordismDistance K₀ K₁ ≤ S.genus :=
  iInf_le _ S

/-- A lower bound for the cobordism distance is a lower bound for the genus of every knot
cobordism. -/
@[simp]
theorem le_cobordismDistance_iff {m : ℕ∞} :
    m ≤ cobordismDistance K₀ K₁ ↔ ∀ S : KnotCobordism K₀ K₁, m ≤ S.genus :=
  le_iInf_iff

/-- The cobordism distance is attained when a knot cobordism exists. -/
theorem exists_genus_eq_cobordismDistance [Nonempty (KnotCobordism K₀ K₁)] :
    ∃ S : KnotCobordism K₀ K₁, (S.genus : ℕ∞) = cobordismDistance K₀ K₁ :=
  ENat.exists_eq_iInf _

/-- The cobordism distance is finite exactly when a knot cobordism exists. -/
@[simp]
theorem cobordismDistance_lt_top_iff :
    cobordismDistance K₀ K₁ < ⊤ ↔ Nonempty (KnotCobordism K₀ K₁) :=
  ENat.iInf_natCast_lt_top

/-- The cobordism distance only depends on the images of the knots. -/
theorem cobordismDistance_congr_range (h₀ : range K₀ = range K₀') (h₁ : range K₁ = range K₁') :
    cobordismDistance K₀ K₁ = cobordismDistance K₀' K₁' := by
  refine le_antisymm (le_iInf fun S => ?_) (le_iInf fun S => ?_)
  · simpa using cobordismDistance_le_genus (S.congrRange h₀.symm h₁.symm)
  · simpa using cobordismDistance_le_genus (S.congrRange h₀ h₁)

/-- **Concordant knots are at cobordism distance `0`**: a concordance is a cobordism of genus
`0`. -/
theorem SmoothEmbedding.Concordant.cobordismDistance_eq_zero
    (h : SmoothEmbedding.Concordant K₀ K₁) : cobordismDistance K₀ K₁ = 0 := by
  obtain ⟨F⟩ := SmoothEmbedding.concordant_iff_nonempty.1 h
  simpa using cobordismDistance_le_genus (ofConcordance F)

/-- A knot is at cobordism distance `0` from itself. -/
@[simp]
theorem cobordismDistance_self (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance K K = 0 :=
  SmoothEmbedding.Concordant.cobordismDistance_eq_zero
    (.of_concordance (SmoothEmbedding.Concordance.refl K))

/-- **The cobordism distance is symmetric**: reversing the heights turns a knot cobordism from `K₀`
to `K₁` into one from `K₁` to `K₀` of the same genus. -/
theorem cobordismDistance_comm (K₀ K₁ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    cobordismDistance K₀ K₁ = cobordismDistance K₁ K₀ :=
  le_antisymm (le_iInf fun S ↦ by simpa using cobordismDistance_le_genus S.symm)
    (le_iInf fun S ↦ by simpa using cobordismDistance_le_genus S.symm)

/-- **The cobordism distance is a concordance invariant**: composing knot cobordisms with
concordances at either end keeps their genus, so concordant knots are at the same cobordism
distance from concordant knots. -/
theorem cobordismDistance_congr_concordant (h₀ : SmoothEmbedding.Concordant K₀ K₀')
    (h₁ : SmoothEmbedding.Concordant K₁ K₁') :
    cobordismDistance K₀ K₁ = cobordismDistance K₀' K₁' := by
  obtain ⟨C₀⟩ := SmoothEmbedding.concordant_iff_nonempty.1 h₀
  obtain ⟨C₁⟩ := SmoothEmbedding.concordant_iff_nonempty.1 h₁
  refine le_antisymm (le_iInf fun S ↦ ?_) (le_iInf fun S ↦ ?_)
  · simpa using cobordismDistance_le_genus (C₀.transKnotCobordism (S.transConcordance C₁.symm))
  · simpa using cobordismDistance_le_genus (C₀.symm.transKnotCobordism (S.transConcordance C₁))

/-- The cobordism distance does not depend on the rotation of the parametrization of the first
knot. -/
@[simp]
theorem cobordismDistance_rotate_left (a : Circle) :
    cobordismDistance (K₀.rotate a) K₁ = cobordismDistance K₀ K₁ :=
  cobordismDistance_congr_range (K₀.range_rotate a) rfl

/-- The cobordism distance does not depend on the rotation of the parametrization of the second
knot. -/
@[simp]
theorem cobordismDistance_rotate_right (a : Circle) :
    cobordismDistance K₀ (K₁.rotate a) = cobordismDistance K₀ K₁ :=
  cobordismDistance_congr_range rfl (K₁.range_rotate a)

/-- The cobordism distance does not depend on the orientation of the first knot. -/
@[simp]
theorem cobordismDistance_reverse_left :
    cobordismDistance K₀.reverse K₁ = cobordismDistance K₀ K₁ :=
  cobordismDistance_congr_range K₀.range_reverse rfl

/-- The cobordism distance does not depend on the orientation of the second knot. -/
@[simp]
theorem cobordismDistance_reverse_right :
    cobordismDistance K₀ K₁.reverse = cobordismDistance K₀ K₁ :=
  cobordismDistance_congr_range rfl K₁.range_reverse

/-- The cobordism distance is invariant under diffeomorphisms of the ambient spheres: transporting
both knots along `Ψ : Sⁿ ≃ₘ Sⁿ` does not change their cobordism distance. -/
@[simp]
theorem cobordismDistance_transDiffeomorph {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [Fact (finrank ℝ F = n + 1)]
    (Ψ : sphere (0 : E) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : F) 1) :
    cobordismDistance (K₀.transDiffeomorph Ψ) (K₁.transDiffeomorph Ψ) =
      cobordismDistance K₀ K₁ := by
  have hK (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
      range ((K.transDiffeomorph Ψ).transDiffeomorph Ψ.symm) = range K := by
    rw [SmoothEmbedding.transDiffeomorph_transDiffeomorph, Diffeomorph.self_trans_symm,
      SmoothEmbedding.transDiffeomorph_refl]
  refine le_antisymm (le_iInf fun S ↦ ?_) (le_iInf fun S ↦ ?_)
  · simpa using cobordismDistance_le_genus (S.transDiffeomorph Ψ)
  · simpa using cobordismDistance_le_genus ((S.transDiffeomorph Ψ.symm).congrRange (hK K₀) (hK K₁))

end TauCeti
