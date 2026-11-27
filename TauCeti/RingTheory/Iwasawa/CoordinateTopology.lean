/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Iwasawa.CompletedCoordinate
public import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.FiniteModule

import Mathlib.Algebra.CharP.Quotient
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.OneAddXPow
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The topology of the Iwasawa coordinate

The level coordinates are continuous from the maximal-ideal-adic topology on `O⟦X⟧` to the
coefficient-adic topology on the finite group algebras. For noetherian `O`, the completed
coordinate is a homeomorphism for the inverse-limit topology. The forward comparison uses
nilpotence modulo the coefficient maximal ideal at each level, and the reverse comparison uses
`PowerSeries.one_add_X_pow_sub_one_mem_maximalIdeal_pow` to control the level kernels.

See Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Proposition (5.3.5).
-/

public section

open Filter IsLocalRing PowerSeries Topology

namespace TauCeti.Iwasawa

open completedGroupAlgebra

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [IsLocalRing O]
  [IsAdicComplete (maximalIdeal O) O]
  (hp : (p : O) ∈ maximalIdeal O)

local notation "Λ" => O⟦X⟧
local notation "B" n => MonoidAlgebra O (Multiplicative (ZMod (p ^ n)))

/-- At level `n`, the `p ^ n`-th power of the image of the parameter lies in the extended
coefficient maximal ideal. -/
theorem levelCoordinate_X_pow_mem (n : ℕ) :
    levelCoordinate hp n X ^ p ^ n ∈ (maximalIdeal O).map (algebraMap O (B n)) := by
  let I : Ideal O := Ideal.span {(p : O)}
  let φ : Λ →+* B n := levelCoordinate hp n
  have : CharP (O ⧸ I) p := CharP.quotient O p (mem_nonunits_iff.mpr hp)
  have hfg : (RingHom.ker (Ideal.Quotient.mk I)).FG := by
    rw [Ideal.mk_ker]
    exact Submodule.fg_span_singleton _
  have hmem : (X : Λ) ^ p ^ n - ((1 + X) ^ p ^ n - 1) ∈ I.map (algebraMap O Λ) := by
    -- Reduction modulo `p` identifies the cyclotomic relation with `X ^ p ^ n`.
    rw [PowerSeries.algebraMap_eq, ← Ideal.mk_ker (I := I), ← ker_map_of_fg _ hfg, RingHom.mem_ker]
    simp only [map_sub, map_pow, map_X, map_add, map_one, one_add_X_pow_sub_one_eq_X_pow, sub_self]
  have hω : φ ((1 + X) ^ p ^ n - 1) = 0 :=
    (levelCoordinate_eq_zero_iff hp n _).mpr (dvd_refl _)
  have hm := Ideal.mem_map_of_mem φ hmem
  rw [Ideal.map_map, (levelCoordinate hp n).comp_algebraMap, map_sub, map_pow, hω, sub_zero] at hm
  exact Ideal.map_mono ((Ideal.span_singleton_le_iff_mem _).mpr hp) hm

/-- The level coordinate is continuous for the maximal-ideal-adic topology on `O⟦X⟧` and
the module topology (equivalently the coefficient maximal-ideal-adic topology) at level `n`. -/
theorem continuous_levelCoordinate (n : ℕ) [TopologicalSpace O] [TopologicalSpace Λ]
    [TopologicalSpace (B n)] [IsModuleTopology O (B n)]
    (hO : IsAdic (maximalIdeal O)) (hΛ : IsAdic (maximalIdeal Λ)) :
    Continuous (levelCoordinate hp n) := by
  let J := (maximalIdeal O).map (algebraMap O (B n))
  let φ : Λ →+* B n := levelCoordinate hp n
  have hB : Module.Finite O (B n) := Module.Finite.of_basis (MonoidAlgebra.basis _ O)
  have : IsTopologicalRing O := hO ▸ (maximalIdeal O).nonarchimedean.toIsTopologicalRing
  have hJ : IsAdic J := by
    have hJGroup : @IsTopologicalAddGroup (B n) J.adicTopology _ := by
      let _ := J.adicTopology
      have := J.nonarchimedean.toIsTopologicalRing
      infer_instance
    refine IsTopologicalAddGroup.ext (IsModuleTopology.isTopologicalAddGroup O (B n)) hJGroup ?_
    apply (hO.hasBasis_nhds_zero_pow_smul (M := B n)).eq_of_same_basis
    simpa only [J, Ideal.map_pow, Ideal.smul_top_eq_map, Ideal.coe_restrictScalars] using
      J.hasBasis_nhds_zero_adic
  have hgen := TauCeti.PowerSeries.maximalIdeal_eq_span_insert_X (maximalIdeal O).span_eq
  have hmap : (maximalIdeal Λ).map φ = Ideal.span {φ X} ⊔ J := by
    -- The generators are the image of `X` and the extended coefficient ideal.
    rw [hgen, Ideal.span_insert, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    rw [← Ideal.map_span, Ideal.map_map, ← PowerSeries.algebraMap_eq,
      (levelCoordinate hp n).comp_algebraMap, Ideal.span_eq]
  refine (hΛ.continuous_iff_exists_pos_pow_map_le hJ (f := φ)).mpr
    ⟨p ^ n + 1, Nat.succ_pos _, ?_⟩
  rw [Ideal.map_pow, hmap]
  exact Ideal.sup_pow_add_le_pow_sup_pow.trans <| sup_le
    (by rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
        exact levelCoordinate_X_pow_mem hp n)
    (pow_one J).le

/-- At a sufficiently deep level, membership in the extended coefficient ideal power forces
the series to lie in the corresponding power of the power-series maximal ideal. -/
theorem comap_levelCoordinate_map_maximalIdeal_pow_le {k n : ℕ} (hkn : k ≤ n + 1) :
    ((maximalIdeal O ^ k).map (algebraMap O (B n))).comap (levelCoordinate hp n).toRingHom ≤
      maximalIdeal Λ ^ k := by
  have hcoeff : (levelCoordinate hp n).toRingHom.comp (algebraMap O Λ) = algebraMap O (B n) :=
    (levelCoordinate hp n).comp_algebraMap
  rw [← hcoeff, ← Ideal.map_map, Ideal.map_pow]
  have hC : (maximalIdeal O).map (algebraMap O Λ) ≤ maximalIdeal Λ := by
    rw [PowerSeries.algebraMap_eq, Ideal.map_le_iff_le_comap,
      TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff, Ideal.comap_comap,
      constantCoeff_comp_C, Ideal.comap_id]
  refine (Ideal.comap_mono (Ideal.map_mono (Ideal.pow_right_mono hC k))).trans ?_
  have hker : RingHom.ker (levelCoordinate hp n).toRingHom =
      Ideal.span {(1 + X : Λ) ^ p ^ n - 1} := ker_levelCoordinate hp n
  rw [Ideal.comap_map_of_surjective (levelCoordinate hp n).toRingHom
    (levelCoordinate_surjective hp n), ← RingHom.ker_eq_comap_bot, sup_le_iff, hker,
    Ideal.span_singleton_le_iff_mem]
  exact ⟨le_rfl, Ideal.pow_le_pow_right hkn (one_add_X_pow_sub_one_mem_maximalIdeal_pow hp n)⟩

/-- The completed coordinate identifies the maximal-ideal-adic topology on `O⟦X⟧` with
the inverse-limit topology on the completed group algebra of `ℤ_p`. -/
theorem isHomeomorph_completedCoordinateEquiv [IsNoetherianRing O] [TopologicalSpace O]
    [TopologicalSpace Λ] (hO : IsAdic (maximalIdeal O)) (hΛ : IsAdic (maximalIdeal Λ)) :
    IsHomeomorph (completedCoordinateEquiv hp) := by
  have : IsTopologicalRing O := hO ▸ (maximalIdeal O).nonarchimedean.toIsTopologicalRing
  have : IsTopologicalRing Λ := hΛ ▸ (maximalIdeal Λ).nonarchimedean.toIsTopologicalRing
  let _ (n : ℕ) : TopologicalSpace (B n) := moduleTopology O (B n)
  let T := FiniteQuotientTower.padicTower p
  let e := completedCoordinateEquiv hp
  have hproj (n : ℕ) (F : Λ) : towerProj O T n (e F) = levelCoordinate hp n F := by
    rw [coe_completedCoordinateEquiv, towerProj_completedCoordinate]
  have hf : Continuous e := (continuous_iff_towerProj (R := O) (T := T)).mpr fun n ↦
    (continuous_levelCoordinate hp n hO hΛ).congr (fun F ↦ (hproj n F).symm)
  have hback : Continuous e.symm := by
    apply continuous_of_tendsto_nhds_zero e.symm.toAddEquiv
    rw [hΛ.hasBasis_nhds_zero.tendsto_right_iff]
    intro k _
    have hfin : Module.Finite O (B k) := Module.Finite.of_basis (MonoidAlgebra.basis _ O)
    have hk : ((maximalIdeal O ^ k • ⊤ : Submodule O (B k)) : Set (B k)) ∈ 𝓝 0 :=
      hO.hasBasis_nhds_zero_pow_smul.mem_of_mem (i := k) trivial
    have ht := (continuous_towerProj (R := O) (T := T) k).continuousAt (x := 0)
    rw [ContinuousAt, map_zero] at ht
    filter_upwards [ht hk] with x hx
    have hxk : towerProj O T k x ∈ (maximalIdeal O ^ k • ⊤ : Submodule O (B k)) := hx
    have hs : e.symm x ∈ ((maximalIdeal O ^ k).map (algebraMap O (B k))).comap
        (levelCoordinate hp k).toRingHom := by
      have he : (levelCoordinate hp k).toRingHom (e.symm x) = towerProj O T k x := by
        exact (hproj k _).symm.trans (congrArg (towerProj O T k) (e.apply_symm_apply x))
      rw [Ideal.mem_comap, he]
      simpa only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem] using hxk
    exact comap_levelCoordinate_map_maximalIdeal_pow_le hp k.le_succ hs
  exact (Homeomorph.mk e.toEquiv hf hback).isHomeomorph

end TauCeti.Iwasawa
