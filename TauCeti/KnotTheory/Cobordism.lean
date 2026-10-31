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
public import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
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
`TauCeti.cobordismDistance_mirror` in `TauCeti.KnotTheory.Mirror`. The triangle inequality, which
stacks two cobordisms and so glues their surfaces along the common collar, is not proved here.

## Main definitions

* `TauCeti.KnotCobordism K₀ K₁`: a smooth knot cobordism from `K₀` to `K₁`, in collared form.
* `TauCeti.KnotCobordism.genus`: the genus `⌊dim H₁(S; ℚ) / 2⌋` of a knot cobordism.
* `TauCeti.KnotCobordism.ofConcordance`: the cobordism traced by a concordance.
* `TauCeti.KnotCobordism.symm`: the reverse of a knot cobordism, with heights reflected.
* `TauCeti.KnotCobordism.transDiffeomorph`: the transport of a knot cobordism along an ambient
  diffeomorphism.
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

end KnotCobordism

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
