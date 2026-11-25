/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.KnotTheory.Khovanov.Homology
public import TauCeti.KnotTheory.Khovanov.Resolution.Support
public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Adequate

/-!
# Khovanov homology of adequate diagrams in the extreme degrees

Let `D` be a planar diagram with `n` crossings, whose all-A and all-B smoothings have `kA` and
`kB` circles. The Khovanov complex has quantum support in `[-kA, n + kB]`
(`TauCeti.PDCode.isZero_khovanovBracket_X_of_quantum_notMem_Icc`). In cochain height `0` the only
state is the all-A state, and its only labelling of quantum degree `-kA` labels every circle by
`X`; in height `n` the only state is the all-B state, and its only labelling of quantum degree
`n + kB` labels every circle by `1`.

If `D` is A-adequate, every state adjacent to the all-A state has `kA - 1` circles, so no
enhanced state of height `1` reaches quantum degree `-kA`. Nothing lies below height `0`, so the
single all-`X` generator survives in homology: `H⁰` of the bracket in quantum degree `-kA` is free
of rank one. Dually, if `D` is B-adequate, no
enhanced state of height `n - 1` reaches quantum degree `n + kB`, and the all-`1` generator of the
all-B state spans `Hⁿ` in that quantum degree.

After normalization these are the bidegrees `(-n₋, n₊ - 2n₋ - kA)` and
`(n₊, n₊ - 2n₋ + n + kB)`, the two extreme cochain degrees `-n₋` and `n₊` of the normalized
complex. So the Khovanov homology of an adequate diagram is nonzero in both extreme cochain
degrees; this is the input to the crossing-number bound for adequate diagrams.

## Main results

* `TauCeti.PDCode.khovanovBracketHomologyAllAIso`,
  `TauCeti.PDCode.khovanovBracketHomologyAllBIso`: the bracket homology of an A-adequate
  (B-adequate) diagram in its lowest (highest) quantum degree and extreme height is `R`.
* `TauCeti.OrientedPDCode.khovanovHomologyAllAIso`,
  `TauCeti.OrientedPDCode.khovanovHomologyAllBIso`: the normalized versions,
  `Kh^{-n₋, n₊ - 2n₋ - kA}(D; R) ≅ R` and `Kh^{n₊, n₊ - 2n₋ + n + kB}(D; R) ≅ R`.
* `TauCeti.OrientedPDCode.not_isZero_khovanovHomology_of_isAAdequate`,
  `TauCeti.OrientedPDCode.not_isZero_khovanovHomology_of_isBAdequate`: over a nontrivial ring
  these groups are nonzero.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Finset HomologicalComplex

namespace TauCeti

namespace PDCode

universe u

variable {n : ℕ} {D : PDCode n} (hD : D.IsPlanar) (R : Type u) [CommRing R]

/-- **No enhanced state of height `1` reaches the lowest quantum degree** of an A-adequate
diagram: the bracket vanishes in height `1` and quantum degree `-kA`. -/
theorem IsAAdequate.isZero_khovanovBracket_X_one (hA : D.IsAAdequate) :
    IsZero ((D.khovanovBracket hD R (-(D.stateLoopCount (cubeState ∅) : ℤ))).X 1) := by
  rw [khovanovBracket_apply, Functor.isZero_cubeComplex_X_iff]
  rintro ⟨S, hS⟩
  dsimp only
  obtain ⟨c, rfl⟩ := card_eq_one.1 (by exact_mod_cast hS : #S = 1)
  rw [resolutionCube_obj, ModuleCat.isZero_of_iff_subsingleton, Submodule.subsingleton_iff_eq_bot]
  refine Khovanov.circleQuantumGrading_piece_eq_bot fun l hl ↦ ?_
  have hk := hA.stateLoopCount_add_one (t := cubeState {c}) (c := c)
    (fun j hj ↦ by simp [cubeState_apply, hj]) (by simp [cubeState_apply])
  rw [← cubeState_empty] at hk
  have hlabel := Khovanov.abs_labelingQuantumDegree_le l
  rw [card_resolvedCircle, abs_le] at hlabel
  rw [card_singleton] at hl
  omega

/-- **No enhanced state of height `n - 1` reaches the highest quantum degree** of a B-adequate
diagram: the bracket vanishes in height `n - 1` and quantum degree `n + kB`. -/
theorem IsBAdequate.isZero_khovanovBracket_X_sub_one (hB : D.IsBAdequate) :
    IsZero ((D.khovanovBracket hD R (n + D.stateLoopCount (cubeState univ))).X (n - 1)) := by
  rw [khovanovBracket_apply, Functor.isZero_cubeComplex_X_iff]
  rintro ⟨S, hS⟩
  dsimp only
  have hSc : #Sᶜ = 1 := by
    rw [card_compl, Fintype.card_fin]
    omega
  obtain ⟨c, hc⟩ := card_eq_one.1 hSc
  have hmem (j : Fin n) : j ∈ S ↔ j ≠ c := by
    rw [ne_eq, ← mem_singleton, ← hc, mem_compl, not_not]
  rw [resolutionCube_obj, ModuleCat.isZero_of_iff_subsingleton, Submodule.subsingleton_iff_eq_bot]
  refine Khovanov.circleQuantumGrading_piece_eq_bot fun l hl ↦ ?_
  have hk := hB.stateLoopCount_add_one (t := cubeState S) (c := c)
    (fun j hj ↦ by simp [cubeState_apply, hmem, hj]) (by simp [cubeState_apply, hmem])
  rw [← cubeState_univ] at hk
  have hlabel := Khovanov.abs_labelingQuantumDegree_le l
  rw [card_resolvedCircle, abs_le] at hlabel
  omega

/-- **The lowest quantum degree of an A-adequate diagram**: its bracket homology in height `0` and
quantum degree `-kA` is `R`, spanned by the all-A state labelled `X` on every circle. -/
def khovanovBracketHomologyAllAIso (hA : D.IsAAdequate) :
    (D.khovanovBracket hD R (-(D.stateLoopCount (cubeState ∅) : ℤ))).homology 0 ≅
      ModuleCat.of R R :=
  have h₀ : IsZero ((D.khovanovBracket hD R (-(D.stateLoopCount (cubeState ∅) : ℤ))).X (-1)) := by
    rw [khovanovBracket_apply]
    exact (D.resolutionCube hD R _).isZero_cubeComplex_X_of_neg (by simp)
  ((D.khovanovBracket hD R _).XIsoHomologyOfDEqZero 0
      (by rw [CochainComplex.prev, zero_sub]; exact h₀.eq_of_src _ _)
      (by rw [CochainComplex.next, zero_add]
          exact (hA.isZero_khovanovBracket_X_one hD R).eq_of_tgt _ _)).symm ≪≫
    eqToIso (by rw [khovanovBracket_apply]) ≪≫
    (D.resolutionCube hD R _).cubeComplexXZeroIso ≪≫
    eqToIso (D.resolutionCube_obj hD R _ ∅) ≪≫
    (Khovanov.circlePieceEquivOfUnique R (fun _ ↦ true) fun l ↦ by
      rw [card_empty, Nat.cast_zero, sub_zero, ← card_resolvedCircle,
        Khovanov.labelingQuantumDegree_eq_neg_card_iff]).toModuleIso

/-- The identification of the lowest-degree bracket homology of an A-adequate diagram with `R`
reads off the coefficient of a cocycle along the all-A state labelled `X` on every circle. -/
@[reassoc (attr := simp)]
theorem homologyπ_khovanovBracketHomologyAllAIso_hom (hA : D.IsAAdequate) :
    (D.khovanovBracket hD R (-(D.stateLoopCount (cubeState ∅) : ℤ))).homologyπ 0 ≫
        (khovanovBracketHomologyAllAIso hD R hA).hom =
      (D.khovanovBracket hD R _).iCycles 0 ≫ eqToHom (by rw [khovanovBracket_apply]) ≫
        (D.resolutionCube hD R (-(D.stateLoopCount (cubeState ∅) : ℤ))).cubeComplexXZeroIso.hom ≫
          eqToHom (D.resolutionCube_obj hD R _ ∅) ≫
            ModuleCat.ofHom ((Khovanov.circleBasis R _).coord (fun _ ↦ true) ∘ₗ
              Submodule.subtype _) := by
  simp only [khovanovBracketHomologyAllAIso, Iso.trans_hom, Iso.symm_hom,
    XIsoHomologyOfDEqZero_inv, eqToIso.hom, LinearEquiv.toModuleIso_hom, Category.assoc]
  rw [isoHomologyπ_hom_inv_id_assoc]
  ext x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
    Khovanov.circlePieceEquivOfUnique_apply, Module.Basis.coord_apply, Submodule.subtype_apply]

/-- **The highest quantum degree of a B-adequate diagram**: its bracket homology in height `n` and
quantum degree `n + kB` is `R`, spanned by the all-B state labelled `1` on every circle. -/
def khovanovBracketHomologyAllBIso (hB : D.IsBAdequate) :
    (D.khovanovBracket hD R (n + D.stateLoopCount (cubeState univ))).homology n ≅
      ModuleCat.of R R :=
  have h₀ :
      IsZero ((D.khovanovBracket hD R (n + D.stateLoopCount (cubeState univ))).X (n + 1)) := by
    rw [khovanovBracket_apply]
    exact (D.resolutionCube hD R _).isZero_cubeComplex_X_of_card_lt (by simp)
  ((D.khovanovBracket hD R _).XIsoHomologyOfDEqZero n
      (by rw [CochainComplex.prev]
          exact (hB.isZero_khovanovBracket_X_sub_one hD R).eq_of_src _ _)
      (by rw [CochainComplex.next]; exact h₀.eq_of_tgt _ _)).symm ≪≫
    (D.khovanovBracket hD R _).XIsoOfEq (Int.natCast_inj.2 (Fintype.card_fin n).symm) ≪≫
    eqToIso (by rw [khovanovBracket_apply]) ≪≫
    (D.resolutionCube hD R _).cubeComplexXTopIso ≪≫
    eqToIso (D.resolutionCube_obj hD R _ univ) ≪≫
    (Khovanov.circlePieceEquivOfUnique R (fun _ ↦ false) fun l ↦ by
      rw [card_univ, Fintype.card_fin, add_sub_cancel_left, ← card_resolvedCircle,
        Khovanov.labelingQuantumDegree_eq_card_iff]).toModuleIso

/-- The identification of the highest-degree bracket homology of a B-adequate diagram with `R`
reads off the coefficient of a cocycle along the all-B state labelled `1` on every circle. -/
@[reassoc (attr := simp)]
theorem homologyπ_khovanovBracketHomologyAllBIso_hom (hB : D.IsBAdequate) :
    (D.khovanovBracket hD R (n + D.stateLoopCount (cubeState univ))).homologyπ n ≫
        (khovanovBracketHomologyAllBIso hD R hB).hom =
      (D.khovanovBracket hD R _).iCycles n ≫
        ((D.khovanovBracket hD R _).XIsoOfEq (Int.natCast_inj.2 (Fintype.card_fin n).symm)).hom ≫
          eqToHom (by rw [khovanovBracket_apply]) ≫
            (D.resolutionCube hD R (n + D.stateLoopCount (cubeState univ))).cubeComplexXTopIso.hom ≫
              eqToHom (D.resolutionCube_obj hD R _ univ) ≫
                ModuleCat.ofHom ((Khovanov.circleBasis R _).coord (fun _ ↦ false) ∘ₗ
                  Submodule.subtype _) := by
  simp only [khovanovBracketHomologyAllBIso, Iso.trans_hom, Iso.symm_hom,
    XIsoHomologyOfDEqZero_inv, eqToIso.hom, LinearEquiv.toModuleIso_hom, Category.assoc]
  rw [isoHomologyπ_hom_inv_id_assoc]
  ext x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
    Khovanov.circlePieceEquivOfUnique_apply, Module.Basis.coord_apply, Submodule.subtype_apply]

end PDCode

namespace OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

/-- **Khovanov homology of an A-adequate diagram in its lowest cochain degree**: in bidegree
`(-n₋, n₊ - 2n₋ - kA)`, where `kA` is the number of circles of the all-A smoothing, it is `R`. -/
def khovanovHomologyAllAIso (hA : D.toPDCode.IsAAdequate) :
    D.khovanovHomology hD R (-D.negativeCrossingCount)
        (D.positiveCrossingCount - 2 * D.negativeCrossingCount -
          D.toPDCode.stateLoopCount (PDCode.cubeState ∅)) ≅
      ModuleCat.of R R :=
  D.khovanovHomologyIsoCubeComplexHomology hD R hD rfl _ _
      (k := -(D.toPDCode.stateLoopCount (PDCode.cubeState ∅) : ℤ)) (a := 0) (by ring)
      (by ring) ≪≫
    eqToIso (by rw [PDCode.khovanovBracket_apply]) ≪≫
    PDCode.khovanovBracketHomologyAllAIso hD R hA

/-- **Khovanov homology of a B-adequate diagram in its highest cochain degree**: in bidegree
`(n₊, n₊ - 2n₋ + n + kB)`, where `kB` is the number of circles of the all-B smoothing, it is
`R`. -/
def khovanovHomologyAllBIso (hB : D.toPDCode.IsBAdequate) :
    D.khovanovHomology hD R D.positiveCrossingCount
        (D.positiveCrossingCount - 2 * D.negativeCrossingCount + n +
          D.toPDCode.stateLoopCount (PDCode.cubeState univ)) ≅
      ModuleCat.of R R :=
  D.khovanovHomologyIsoCubeComplexHomology hD R hD rfl _ _
      (k := n + D.toPDCode.stateLoopCount (PDCode.cubeState univ)) (a := n) (by ring)
      (by have := D.positiveCrossingCount_add_negativeCrossingCount; omega) ≪≫
    eqToIso (by rw [PDCode.khovanovBracket_apply]) ≪≫
    PDCode.khovanovBracketHomologyAllBIso hD R hB

/-- **The Khovanov homology of an A-adequate diagram is nonzero in its lowest cochain degree**
`-n₋`, over every nontrivial coefficient ring. -/
theorem not_isZero_khovanovHomology_of_isAAdequate [Nontrivial R]
    (hA : D.toPDCode.IsAAdequate) :
    ¬ IsZero (D.khovanovHomology hD R (-D.negativeCrossingCount)
        (D.positiveCrossingCount - 2 * D.negativeCrossingCount -
          D.toPDCode.stateLoopCount (PDCode.cubeState ∅))) := fun h ↦
  not_subsingleton R (ModuleCat.isZero_of_iff_subsingleton.1
    (h.of_iso (D.khovanovHomologyAllAIso hD R hA).symm))

/-- **The Khovanov homology of a B-adequate diagram is nonzero in its highest cochain degree**
`n₊`, over every nontrivial coefficient ring. -/
theorem not_isZero_khovanovHomology_of_isBAdequate [Nontrivial R]
    (hB : D.toPDCode.IsBAdequate) :
    ¬ IsZero (D.khovanovHomology hD R D.positiveCrossingCount
        (D.positiveCrossingCount - 2 * D.negativeCrossingCount + n +
          D.toPDCode.stateLoopCount (PDCode.cubeState univ))) := fun h ↦
  not_subsingleton R (ModuleCat.isZero_of_iff_subsingleton.1
    (h.of_iso (D.khovanovHomologyAllBIso hD R hB).symm))

end OrientedPDCode

end TauCeti
