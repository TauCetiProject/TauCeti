/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.DihedralSixteen
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.IndexTwoNorm
public import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.IndexTwo

/-!
# The index-two graph cochain as a pullback of the `D₁₆` extension cocycle

Let `U` be a subgroup of index two of a group `G`, let `s` be an element outside `U` and let
`α : U →* Multiplicative (ZMod 2)` be a homomorphism. The two-point graph cochain `ν_α` of
`TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cochain` represents the index-two
Evens norm of `α`. This file identifies `ν_α`, on the nose, with the pullback of the factor set of
the central extension `1 → C₂ → D₁₆ → C₂ ≀ C₂ → 1` plus an explicit coboundary.

The universal case is the base group `U₀ = C₂ × C₂` of `C₂ ≀ C₂` with its tautological character
`(a, b, 0) ↦ a`. At every element `t = (a, 0, 1)` outside `U₀` the two Shapiro components of the
tautological character are the first two coordinates, and the graph cochain is

```text
ν_taut = c_{D₁₆} + δ w,        w (a, b, c) = a + c,
```

where `c_{D₁₆}` is the factor set `TauCeti.wreathD16Cocycle` and `w` is the indicator of
`{u, u v, s, v s}`, with `u = (1, 0, 0)`, `v = (0, 1, 0)` and `s = (0, 0, 1)`
(`TauCeti.ContCohomology.evensGraphCochain_wreath`). This is a finite computation.

For general `U`, `s` and `α`, the **induced homomorphism**
`Ind α : G → C₂ ≀ C₂, γ ↦ (b₁ γ, b_s γ, χ_U γ)`, built from the two Shapiro components and the
character `χ_U` of `U`, is a homomorphism by the cocycle law of the pair `(b₁, b_s)`. It pulls `U₀`
back to `U` and the tautological character back to `α`, and it sends `s` to an element of the form
`(a, 0, 1)`. Hence `ν_α` is the pullback of `ν_taut` along `Ind α`, and so

```text
ν_α = c_{D₁₆} ∘ (Ind α × Ind α) + δ (w ∘ Ind α)
```

(`TauCeti.ContCohomology.evensGraphCochain_eq_indexTwoInd_pullback`). When `U` is open and `α`
is continuous, `Ind α` is locally constant, so both pulled-back functions are continuous. On
classes, the coboundary disappears: the index-two Evens norm of the class of `α` is the class of
the pulled-back `D₁₆` factor set,

```text
N^{Ev}(α) = (Ind α)^* c_{D₁₆}
```

(`TauCeti.ContCohomology.evensNormIndexTwo_eq_ind_pullback`).

Read through the signed-permutation representation `C₂ ≀ C₂ ⊂ O₂`, `Ind α` is the representation
induced from `α`. By Kahn and Serre, the class of `c_{D₁₆}` is the second Stiefel–Whitney class of
that representation of `C₂ ≀ C₂`, so the identity above is the cochain-level form of the statement
that the index-two Evens norm of `α` is `w₂` of the induced representation; the Stiefel–Whitney
reading is not formalised here.

## Main definitions

* `TauCeti.ContCohomology.wreathWitness`: the coboundary witness `w = 1_{{u, uv, s, vs}}`.
* `TauCeti.ContCohomology.indexTwoInd`: the induced homomorphism `Ind α : G →* C₂ ≀ C₂`.

## Main results

* `TauCeti.ContCohomology.evensGraphCochain_wreath`: the universal identity
  `ν_taut = c_{D₁₆} + δ w` on `C₂ ≀ C₂`.
* `TauCeti.ContCohomology.comap_indexTwoInd_wreathBase` and
  `TauCeti.ContCohomology.wreathTautological_indexTwoInd`: `Ind α` pulls the base group back to
  `U` and the tautological character back to `α`.
* `TauCeti.ContCohomology.evensGraphCochain_indexTwoInd`: `ν_α` is the pullback of `ν_taut` along
  `Ind α`.
* `TauCeti.ContCohomology.evensGraphCochain_eq_indexTwoInd_pullback`:
  `ν_α = c_{D₁₆} ∘ (Ind α × Ind α) + δ (w ∘ Ind α)`.
* `TauCeti.ContCohomology.isLocallyConstant_indexTwoInd`,
  `TauCeti.ContCohomology.continuous_wreathD16Cocycle_indexTwoInd` and
  `TauCeti.ContCohomology.continuous_wreathWitness_indexTwoInd`: continuity of the pulled-back
  cocycle and witness.
* `TauCeti.ContCohomology.evensNormIndexTwo_eq_ind_pullback`: the index-two Evens norm of the
  class of `α` is the class of `c_{D₁₆} ∘ (Ind α × Ind α)`.

## References

* B. Kahn, *Classes de Stiefel-Whitney de formes quadratiques et de représentations galoisiennes
  réelles*, Invent. Math. **78** (1984), 223–256, th. I.4.2 and Remarque II.2.3.
* J.-P. Serre, *L'invariant de Witt de la forme Tr(x²)*, Comment. Math. Helv. **59** (1984),
  651–676, Théorème 1′.
* A. Kozlowski, *The Evens–Kahn formula for the total Stiefel–Whitney class*, Proc. Amer. Math.
  Soc. **91** (1984), 309–313.
-/

public section

namespace TauCeti.ContCohomology

open Multiplicative WreathC2

universe u

section Universal

/-! ### The universal case: the tautological character of `C₂ ≀ C₂` -/

variable {t : WreathC2}

/-- The tautological character extended by zero is `a (1 + c)` on coordinates. -/
private theorem evensExtend_wreathTautological (g : WreathC2) :
    evensExtend wreathBase wreathTautological g = coordA g * (1 + coordC g) := by
  by_cases h : g ∈ wreathBase
  · rw [evensExtend_of_mem h, toAdd_wreathTautological, mem_wreathBase_iff.1 h, add_zero,
      mul_one]
  · rw [evensExtend_of_notMem h, notMem_wreathBase_iff.1 h]
    generalize coordA g = a
    revert a
    decide

/-- **The first Shapiro component of the tautological character is the first coordinate,** at
every element `t = (a, 0, 1)` outside the base group. -/
theorem evensB1_wreath (hB : coordB t = 0) (hC : coordC t = 1) (g : WreathC2) :
    evensB1 wreathBase t wreathTautological g = coordA g := by
  by_cases h : g ∈ wreathBase
  · rw [evensB1_of_mem h, evensExtend_wreathTautological, mem_wreathBase_iff.1 h, add_zero,
      mul_one]
  · rw [evensB1_of_notMem h, evensExtend_wreathTautological, coordA_mul, coordC_mul, hB, hC,
      notMem_wreathBase_iff.1 h]
    generalize coordA g = a
    generalize coordA t = a'
    revert a a'
    decide

/-- **The second Shapiro component of the tautological character is the second coordinate,** at
every element `t = (a, 0, 1)` outside the base group. -/
theorem evensBs_wreath (hB : coordB t = 0) (hC : coordC t = 1) (g : WreathC2) :
    evensBs wreathBase t wreathTautological g = coordB g := by
  rw [evensBs_apply, evensB1_wreath hB hC, coordA_mul, coordA_inv, coordC_inv, hB, hC]
  generalize coordA g = a
  generalize coordB g = b
  generalize coordA t = a'
  revert a b a'
  decide

/-- **The coboundary witness** `w = 1_{{u, uv, s, vs}}` on `C₂ ≀ C₂`, which on coordinates is
`a + c` (`TauCeti.ContCohomology.wreathWitness_eq_one_iff`). Its coboundary is the difference
between the graph cochain of the tautological character and the `D₁₆` extension cocycle. -/
def wreathWitness (g : WreathC2) : ZMod 2 := coordA g + coordC g

/-- The witness is the indicator of `{u, uv, s, vs}`, with `u = (1, 0, 0)`, `v = (0, 1, 0)` and
`s = (0, 0, 1)`. -/
theorem wreathWitness_eq_one_iff (g : WreathC2) :
    wreathWitness g = 1 ↔
      g = mk 1 0 0 ∨ g = mk 1 0 0 * mk 0 1 0 ∨ g = mk 0 0 1 ∨ g = mk 0 1 0 * mk 0 0 1 := by
  rw [← mk_coordA_coordB_coordC g]
  simp only [wreathWitness, coordA_mk, coordC_mk, mk_mul_mk, mk_inj]
  generalize coordA g = a
  generalize coordB g = b
  generalize coordC g = c
  revert a b c
  decide

/-- **The universal identity:** the graph cochain of the tautological character of `C₂ ≀ C₂`, at
every element `t = (a, 0, 1)` outside the base group, is the `D₁₆` extension cocycle plus the
coboundary of the witness, `ν_taut = c_{D₁₆} + δ w`. This is an identity of cochains; the
consequence that the index-two Evens norm of the tautological character is the class of the
extension `D₁₆ → C₂ ≀ C₂` needs passing from cochains to classes and is not formalised here. -/
theorem evensGraphCochain_wreath (hB : coordB t = 0) (hC : coordC t = 1) (g h : WreathC2) :
    evensGraphCochain wreathBase t wreathTautological (g, h) =
      wreathD16Cocycle (g, h) + (wreathWitness h - wreathWitness (g * h) + wreathWitness g) := by
  rw [wreathD16Cocycle_apply]
  simp only [wreathWitness, coordA_mul, coordC_mul]
  by_cases hg : g ∈ wreathBase
  · rw [evensGraphCochain_of_mem hg, evensB1_wreath hB hC, evensBs_wreath hB hC,
      mem_wreathBase_iff.1 hg]
    generalize coordA g = a₁; generalize coordB g = b₁
    generalize coordA h = a₂; generalize coordB h = b₂; generalize coordC h = c₂
    revert a₁ b₁ a₂ b₂ c₂
    decide
  · rw [evensGraphCochain_of_notMem hg, evensB1_wreath hB hC, evensB1_wreath hB hC,
      evensBs_wreath hB hC, notMem_wreathBase_iff.1 hg]
    generalize coordA g = a₁; generalize coordB g = b₁
    generalize coordA h = a₂; generalize coordB h = b₂; generalize coordC h = c₂
    revert a₁ b₁ a₂ b₂ c₂
    decide

end Universal

section IndexTwoInd

/-! ### The induced homomorphism `Ind α : G → C₂ ≀ C₂` -/

variable {G : Type u} [Group G] (U : Subgroup G) (hU : U.index = 2) (s : G) (hs : s ∉ U)
  (α : U →* Multiplicative (ZMod 2))

/-- **The induced homomorphism `Ind α : G →* C₂ ≀ C₂`** of a homomorphism `α` on a subgroup `U` of
index two, at an element `s ∉ U`: `γ ↦ (b₁ γ, b_s γ, χ_U γ)`, with `b₁`, `b_s` the two Shapiro
components of `α` and `χ_U` the character of `U`. It is a homomorphism by the cocycle law of the
pair `(b₁, b_s)` in the permutation module `𝔽₂[G ⧸ U]`, which is the multiplication of `C₂ ≀ C₂`
read on coordinates. Read through `C₂ ≀ C₂ ⊂ O₂`, it is the representation induced from `α`. -/
noncomputable def indexTwoInd : G →* WreathC2 :=
  MonoidHom.mk' (fun γ => mk (evensB1 U s α γ) (evensBs U s α γ)
    (toAdd (U.indexTwoCharacter hU γ))) fun γ η => by
    rw [mk_mul_mk, mk_inj, map_mul, toAdd_mul]
    by_cases hγ : γ ∈ U
    · rw [evensB1_mul_of_mem hU hs hγ, evensBs_mul_of_mem hU hs hγ,
        Subgroup.toAdd_indexTwoCharacter_of_mem hU hγ]
      simp
    · rw [evensB1_mul_of_notMem hU hs hγ, evensBs_mul_of_notMem hU hs hγ,
        Subgroup.toAdd_indexTwoCharacter_of_notMem hU hγ]
      generalize evensB1 U s α γ = a; generalize evensBs U s α γ = b
      generalize evensB1 U s α η = a'; generalize evensBs U s α η = b'
      generalize toAdd (U.indexTwoCharacter hU η) = c'
      revert a b a' b' c'
      decide

variable {U hU s hs α}

/-- `Ind α (γ)` has coordinates `(b₁ γ, b_s γ, χ_U γ)`. -/
theorem indexTwoInd_apply (γ : G) :
    indexTwoInd U hU s hs α γ =
      mk (evensB1 U s α γ) (evensBs U s α γ) (toAdd (U.indexTwoCharacter hU γ)) :=
  (rfl)

/-- The first coordinate of `Ind α` is the first Shapiro component `b₁`. -/
@[simp]
theorem coordA_indexTwoInd (γ : G) : coordA (indexTwoInd U hU s hs α γ) = evensB1 U s α γ := by
  rw [indexTwoInd_apply, coordA_mk]

/-- The second coordinate of `Ind α` is the second Shapiro component `b_s`. -/
@[simp]
theorem coordB_indexTwoInd (γ : G) : coordB (indexTwoInd U hU s hs α γ) = evensBs U s α γ := by
  rw [indexTwoInd_apply, coordB_mk]

/-- The third coordinate of `Ind α` is the character `χ_U` of `U`. -/
@[simp]
theorem coordC_indexTwoInd (γ : G) :
    coordC (indexTwoInd U hU s hs α γ) = toAdd (U.indexTwoCharacter hU γ) := by
  rw [indexTwoInd_apply, coordC_mk]

/-- `Ind α (γ)` lies in the base group exactly when `γ` lies in `U`. -/
theorem indexTwoInd_mem_wreathBase_iff {γ : G} :
    indexTwoInd U hU s hs α γ ∈ wreathBase ↔ γ ∈ U := by
  rw [mem_wreathBase_iff, coordC_indexTwoInd, toAdd_eq_zero, Subgroup.indexTwoCharacter_eq_one_iff]

variable (U hU s hs α)

/-- **`Ind α` pulls the base group of `C₂ ≀ C₂` back to `U`.** -/
theorem comap_indexTwoInd_wreathBase : wreathBase.comap (indexTwoInd U hU s hs α) = U :=
  Subgroup.ext fun _ => indexTwoInd_mem_wreathBase_iff

/-- **`Ind α` pulls the tautological character back to `α`:** on `U`, which `Ind α` maps into the
base group, the first coordinate of `Ind α` is `α`. -/
theorem coordA_indexTwoInd_coe (γ : U) : coordA (indexTwoInd U hU s hs α γ) = toAdd (α γ) := by
  rw [coordA_indexTwoInd, evensB1_of_mem γ.2, evensExtend_of_mem γ.2]

/-- **`Ind α` pulls the tautological character back to `α`**, as homomorphisms on
`wreathBase.comap (Ind α)`, which is identified with `U` by
`TauCeti.ContCohomology.comap_indexTwoInd_wreathBase`. -/
theorem wreathTautological_indexTwoInd :
    wreathTautological.comp ((indexTwoInd U hU s hs α).subgroupComap wreathBase) =
      α.comp (MulEquiv.subgroupCongr (comap_indexTwoInd_wreathBase U hU s hs α)).toMonoidHom :=
  MonoidHom.ext fun γ => toAdd.injective <| by
    rw [MonoidHom.comp_apply, toAdd_wreathTautological]
    exact coordA_indexTwoInd_coe U hU s hs α (MulEquiv.subgroupCongr _ γ)

/-- The second coordinate of `Ind α (s)` vanishes: `b_s (s) = b₁ (1) = 0`. -/
theorem coordB_indexTwoInd_self : coordB (indexTwoInd U hU s hs α s) = 0 := by
  rw [coordB_indexTwoInd, evensBs_apply, inv_mul_cancel, evensB1_of_mem U.one_mem,
    evensExtend_of_mem U.one_mem]
  exact congrArg toAdd (map_one α)

/-- The third coordinate of `Ind α (s)` is `1`: `Ind α (s)` lies outside the base group. -/
theorem coordC_indexTwoInd_self : coordC (indexTwoInd U hU s hs α s) = 1 := by
  rw [coordC_indexTwoInd, Subgroup.toAdd_indexTwoCharacter_of_notMem hU hs]

/-- The graph cochain is unchanged by transporting `α` along an equality of subgroups. -/
private theorem evensGraphCochain_subgroupCongr {V W : Subgroup G} (e : V = W) (t : G)
    (β : W →* Multiplicative (ZMod 2)) (q : G × G) :
    evensGraphCochain V t (β.comp (MulEquiv.subgroupCongr e).toMonoidHom) q =
      evensGraphCochain W t β q := by
  subst e
  rfl

/-- **The graph cochain of `α` is the pullback along `Ind α` of the graph cochain of the
tautological character,** taken at `Ind α (s)`. -/
theorem evensGraphCochain_indexTwoInd (g h : G) :
    evensGraphCochain U s α (g, h) =
      evensGraphCochain wreathBase (indexTwoInd U hU s hs α s) wreathTautological
        (indexTwoInd U hU s hs α g, indexTwoInd U hU s hs α h) := by
  rw [← evensGraphCochain_comap, wreathTautological_indexTwoInd, evensGraphCochain_subgroupCongr]

/-- **The index-two graph cochain is the pulled-back `D₁₆` extension cocycle plus a pulled-back
coboundary,** on the nose: `ν_α = c_{D₁₆} ∘ (Ind α × Ind α) + δ (w ∘ Ind α)`, with `w` the witness
`TauCeti.ContCohomology.wreathWitness`. -/
theorem evensGraphCochain_eq_indexTwoInd_pullback (g h : G) :
    evensGraphCochain U s α (g, h) =
      wreathD16Cocycle (indexTwoInd U hU s hs α g, indexTwoInd U hU s hs α h) +
        (wreathWitness (indexTwoInd U hU s hs α h) -
          wreathWitness (indexTwoInd U hU s hs α (g * h)) +
          wreathWitness (indexTwoInd U hU s hs α g)) := by
  rw [evensGraphCochain_indexTwoInd U hU s hs α,
    evensGraphCochain_wreath (coordB_indexTwoInd_self U hU s hs α)
      (coordC_indexTwoInd_self U hU s hs α), map_mul]

/-- **`Ind α` is locally constant** when `U` is open and `α` is continuous: its three coordinates
are continuous maps to the discrete `ZMod 2`. -/
theorem isLocallyConstant_indexTwoInd [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) :
    IsLocallyConstant (indexTwoInd U hU s hs α) := by
  have hcoord : IsLocallyConstant fun γ =>
      (evensB1 U s α γ, evensBs U s α γ, toAdd (U.indexTwoCharacter hU γ)) :=
    (IsLocallyConstant.iff_continuous _).2 <|
      (continuous_evensB1 U s α hopen hα).prodMk <| (continuous_evensBs U s α hopen hα).prodMk <|
        continuous_toAdd.comp (Subgroup.continuous_indexTwoCharacter hU hopen)
  convert hcoord.comp fun p => mk p.1 p.2.1 p.2.2 using 1
  exact funext indexTwoInd_apply

/-- **The pulled-back `D₁₆` extension cocycle is continuous** when `U` is open and `α` is
continuous. -/
theorem continuous_wreathD16Cocycle_indexTwoInd [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) :
    Continuous fun q : G × G =>
      wreathD16Cocycle (indexTwoInd U hU s hs α q.1, indexTwoInd U hU s hs α q.2) := by
  have h := isLocallyConstant_indexTwoInd U hU s hs α hopen hα
  exact (((h.comp_continuous continuous_fst).prodMk (h.comp_continuous continuous_snd)).comp
    wreathD16Cocycle).continuous

/-- **The pulled-back coboundary witness is continuous** when `U` is open and `α` is continuous. -/
theorem continuous_wreathWitness_indexTwoInd [TopologicalSpace G] [SeparatelyContinuousMul G]
    (hopen : IsOpen (U : Set G)) (hα : Continuous α) :
    Continuous fun γ : G => wreathWitness (indexTwoInd U hU s hs α γ) :=
  ((isLocallyConstant_indexTwoInd U hU s hs α hopen hα).comp wreathWitness).continuous

end IndexTwoInd

section NormPullback

/-! ### The index-two norm as the pullback of the `D₁₆` class -/

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- **The index-two Evens norm is the pullback of the `D₁₆` extension class:**
`N^{Ev}(α) = (Ind α)^* c_{D₁₆}`, the class of `c_{D₁₆} ∘ (Ind α × Ind α)`, at every `s ∉ U`.
The norm of the class of `α` is the class of the graph cochain at `s`, which differs from the
pulled-back factor set by the coboundary of `w ∘ Ind α`
(`TauCeti.ContCohomology.evensGraphCochain_eq_indexTwoInd_pullback`). -/
theorem evensNormIndexTwo_eq_ind_pullback (U : OpenSubgroup G) (hU : U.toSubgroup.index = 2)
    (s : G) (hs : s ∉ U) (α : U.toSubgroup →* Multiplicative (ZMod 2)) (hα : Continuous α) :
    evensNormIndexTwo U hU (homClass U.toSubgroup α hα) =
      (trivialF2 G).cochainClass 2
        (inhomogeneousCochain2
          (fun q => wreathD16Cocycle
            (indexTwoInd U.toSubgroup hU s hs α q.1, indexTwoInd U.toSubgroup hU s hs α q.2))
          (continuous_wreathD16Cocycle_indexTwoInd U.toSubgroup hU s hs α U.isOpen' hα))
        (inhomogeneousCochain2_d_eq_zero _ _ fun g h j => by
          simp only [map_mul]
          exact wreathD16Cocycle_isCocycle _ _ _) := by
  rw [evensNormIndexTwo_homClass, graphClass_eq_cochainClass U hU s hs]
  exact cochainClass_inhomogeneousCochain2_eq_of_coboundary _ _ _ _ _
    (continuous_wreathWitness_indexTwoInd U.toSubgroup hU s hs α U.isOpen' hα)
    (evensGraphCochain_eq_indexTwoInd_pullback U.toSubgroup hU s hs α) _ _

end NormPullback

end TauCeti.ContCohomology
