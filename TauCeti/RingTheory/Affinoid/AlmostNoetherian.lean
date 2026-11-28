/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Integral.Presentation.Basic
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.AlmostNoetherian

/-!
# Kiehl's almost noetherianity theorem for integral affinoid presentations

Let `K` be a complete ultrametric normed field with closed unit ball
`K° = Subring.unitClosedBall K`. Over an arbitrary complete ultrametric field `K`, an integral
presentation subring `π(K⟨X⟩°)` or an integral affinoid presentation ring `A₀` need not be
noetherian. Instead, Kiehl's Satz 5.1 holds for every finitely generated `A₀`-module `M` (without
requiring `M` to embed in a `K`-module): for every submodule `N ≤ M` and every `0 < ε < 1`, there
is a single finitely generated `A₀`-submodule `N' ≤ N` containing `c • N` for **all** scalars
`c ∈ K°` with `‖c‖ ≤ ε`.

For the basic integral presentation API see
`TauCeti.RingTheory.Affinoid.Integral.Presentation.Basic`; for ordinary noetherianity when `K°` is
noetherian see `TauCeti.RingTheory.Affinoid.Integral.Presentation.Noetherian`; and for the
corresponding statement directly for quotients of `𝒪[K]⟨X₁, …, Xₙ⟩` see
`TauCeti.RingTheory.Huber.Restricted.AlmostNoetherian`.

## Main results

* `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall`,
  `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall_of_isScalarTower`: Kiehl's Satz 5.1 for
  finitely generated modules over `π(K⟨X⟩°)` in finitely many variables.
* `TauCeti.Huber.IntegralAffinoidPresentation.exists_fg_le_forall_smul_mem`: Kiehl's Satz 5.1 for
  finitely generated modules over a continuous integral affinoid presentation `A₀`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5 (Anhang), Satz 5.1.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105, Springer
  (2014), §6.4, proof of Lemma 5 (pp. 137–138).
-/

public section

namespace AlgHom

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
  {A : Type*} [CommRing A] [Algebra K A]

local notation "Tate " τ:max => IsRestricted.subring (R := K) (fun _ : τ ↦ 1)

/-- **Kiehl's almost noetherianity theorem for integral presentation rings (Satz 5.1).** Let `K` be
a complete ultrametric normed field, `σ` a finite variable set, and `π : K⟨X⟩ →ₐ[K] A` a `K`-algebra
homomorphism with integral presentation subring
`A₀ = (Subring.unitClosedBall (K⟨X⟩)).map (π : K⟨X⟩ →+* A)`. For every finitely generated
`A₀`-module `M`, every submodule `N ≤ M`, and every `0 < ε < 1`, there exists a single finitely
generated `A₀`-submodule `N' ≤ N` containing `c • x` for all `c ∈ K` with `‖c‖ ≤ ε` and all
`x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_map_unitClosedBall [CompleteSpace K] [_root_.Finite σ]
    (π : Tate σ →ₐ[K] A) {M : Type*} [AddCommGroup M]
    [Module ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M]
    [Module.Finite ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M]
    (N : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) M,
      N'.FG ∧ N' ≤ N ∧ ∀ (c : K) (hc : ‖c‖ ≤ ε), ∀ x ∈ N,
        (⟨algebraMap K A c, π.algebraMap_mem_map_unitClosedBall (hc.trans hε1.le)⟩ :
          (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) • x ∈ N' := by
  let φ := (RingEquiv.subringCongr π.range_comp_subtype_unitClosedBall).toRingHom.comp
    ((π : Tate σ →+* A).comp (Subring.unitClosedBall (Tate σ)).subtype).rangeRestrict
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    φ.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall (by
      simpa only [φ, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] using
        (RingEquiv.surjective _).comp (RingHom.rangeRestrict_surjective _)) N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  let c₀ : Subring.unitClosedBall K := ⟨c, Subring.mem_unitClosedBall.mpr (hc.trans hε1.le)⟩
  simpa only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    π.subringCongr_rangeRestrict_unitClosedBallC c₀] using hsmul c₀ hc x hx

/-- Scalar-tower form of `AlgHom.exists_fg_le_forall_smul_mem_map_unitClosedBall`: over a complete
ultrametric normed field `K`, for any `π : K⟨X⟩ →ₐ[K] A` in finitely many variables and any
finitely generated `A₀`-submodule `M` of an ambient `A`-module `E` (with compatible `K`-action,
where `A₀ = π(K⟨X⟩°)`), every `A₀`-submodule `N ≤ M` and every `0 < ε < 1` admit a single finitely
generated `A₀`-submodule `N' ≤ N` containing `c • x` for all `c : K` with `‖c‖ ≤ ε` and all
`x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem_map_unitClosedBall_of_isScalarTower [CompleteSpace K]
    [_root_.Finite σ] (π : Tate σ →ₐ[K] A)
    {E : Type*} [AddCommGroup E] [Module K E] [Module A E] [IsScalarTower K A E]
    {M N : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) E}
    (hM : M.FG) (hNM : N ≤ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule ((Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)) E,
      N'.FG ∧ N' ≤ N ∧ ∀ c : K, ‖c‖ ≤ ε → ∀ x ∈ N, c • x ∈ N' := by
  let A₀ := (Subring.unitClosedBall (Tate σ)).map (π : Tate σ →+* A)
  have : Module.Finite A₀ M := Module.Finite.iff_fg.mpr hM
  obtain ⟨N₀', hfg, hle, hsmul⟩ :=
    π.exists_fg_le_forall_smul_mem_map_unitClosedBall (N.comap M.subtype) hε0 hε1
  refine ⟨N₀'.map M.subtype, hfg.map M.subtype, Submodule.map_le_iff_le_comap.mpr hle,
    fun c hc x hx ↦ ?_⟩
  have hxM : x ∈ M := hNM hx
  refine ⟨_, hsmul c hc ⟨x, hxM⟩ hx, ?_⟩
  rw [map_smul, Submodule.subtype_apply, Subring.smul_def, algebraMap_smul]

end AlgHom

namespace TauCeti.Huber.IntegralAffinoidPresentation

open TauCeti.MvPowerSeries

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type*} [CommRing A] [Algebra K A] [TopologicalSpace A]
  {n : ℕ} {A₀ : Subring A}

/-- **Kiehl's almost noetherianity theorem for an integral affinoid presentation.** Over a
complete nontrivially normed ultrametric field `K`, for any finitely generated `A₀`-module `M`, any
`A₀`-submodule `N ≤ M`, and any `0 < ε < 1`, there exists a finitely generated `A₀`-submodule
`N' ≤ N` containing `P.coeffHom c • x` for all `c : Subring.unitClosedBall K` with `‖(c : K)‖ ≤ ε`
and all `x ∈ N`. -/
theorem exists_fg_le_forall_smul_mem [CompleteSpace K]
    (P : IntegralAffinoidPresentation K A n A₀)
    {M : Type*} [AddCommGroup M] [Module A₀ M] [Module.Finite A₀ M]
    (N : Submodule A₀ M) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ N' : Submodule A₀ M, N'.FG ∧ N' ≤ N ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε → ∀ x ∈ N, P.coeffHom c • x ∈ N' := by
  let ψ : Subring.unitClosedBall
      (_root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) →+* A₀ :=
    P.hom.comp (restrictedMvPowerSeriesCompletionUnitClosedBallEquiv (R := K) n).symm.toRingHom
  obtain ⟨N', hfg, hle, hsmul⟩ :=
    ψ.exists_fg_le_forall_smul_mem_of_surjective_unitClosedBall
      (P.surjective_hom.comp (RingEquiv.surjective _)) N hε0 hε1
  refine ⟨N', hfg, hle, fun c hc x hx ↦ ?_⟩
  have heq : ψ (unitClosedBallC c) = P.coeffHom c := by
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      restrictedMvPowerSeriesCompletionUnitClosedBallEquiv_symm_unitClosedBallC, P.hom_algebraMap]
  exact heq ▸ hsmul c hc x hx

end TauCeti.Huber.IntegralAffinoidPresentation
