/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Topology
public import TauCeti.Topology.Algebra.Group.Profinite.Completion
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP

/-!
# Multiplicative p-adic completion as a maximal pro-p quotient

For a mixed-characteristic nonarchimedean local field `L`, the inverse limit
`A(L) = lim_m Lˣ/(Lˣ)^(p^m)` is canonically the maximal pro-`p` quotient of the profinite
completion `(Lˣ)^` of the abstract group `Lˣ`. The comparison is characterized by sending the
class of a unit to its compatible family of power classes.

Local reciprocity identifies `(Lˣ)^` with the abelianized absolute Galois group of `L`, so this
comparison is the bridge from `A(L)` to the maximal abelian pro-`p` quotient of that Galois group.

## Main declarations

* `TauCeti.maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits`: the canonical
  isomorphism of topological groups from the maximal pro-`p` quotient of `(Lˣ)^` to `A(L)`.
-/

public section

noncomputable section

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [CharZero L]

/-- The continuous extension of `Lˣ → A(L)` to the profinite completion of `Lˣ`. -/
private def profiniteCompletionToPadicCompletionUnits :
    ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Lˣ) →ₜ*
      ↑(padicCompletionUnits p L) :=
  (ProfiniteCompletion.continuousMonoidHomEquiv Lˣ ↑(padicCompletionUnits p L)).symm
    (padicCompletionUnitsOf p L)

private theorem profiniteCompletionToPadicCompletionUnits_etaFn (x : Lˣ) :
    profiniteCompletionToPadicCompletionUnits p L
        (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Lˣ) x) =
      padicCompletionUnitsOf p L x :=
  ProfiniteCompletion.continuousMonoidHomEquiv_symm_apply_etaFn _ _ _ _

private theorem surjective_profiniteCompletionToPadicCompletionUnits :
    Function.Surjective (profiniteCompletionToPadicCompletionUnits p L) :=
  ProfiniteCompletion.surjective_continuousMonoidHom_of_denseRange _ _ <| by
    simpa only [profiniteCompletionToPadicCompletionUnits_etaFn] using
      denseRange_padicCompletionUnitsOf p L

/-- The kernel of `(Lˣ)^ → A(L)` lies in the pro-`p` kernel of `(Lˣ)^`. -/
private theorem mem_proPKernel_of_profiniteCompletionToPadicCompletionUnits_eq_one
    {c : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Lˣ)}
    (hc : profiniteCompletionToPadicCompletionUnits p L c = 1) :
    c ∈ proPKernel p (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Lˣ)) := by
  refine mem_proPKernel_iff.2 fun U hU ↦ ?_
  obtain ⟨m, hm⟩ := isPGroup_iff_exists_pow_pow_eq_one.mp hU
  let η := ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of Lˣ)
  -- The `p ^ m`-th powers of `Lˣ` map into `U`, since the quotient by `U` has exponent
  -- dividing `p ^ m`.
  have hle : (powMonoidHom (p ^ m) : Lˣ →* Lˣ).range ≤ U.toSubgroup.comap η.hom := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_comap, ← QuotientGroup.eq_one_iff, powMonoidHom_apply, map_pow,
      QuotientGroup.mk_pow]
    exact hm _
  let e := QuotientGroup.map _ U.toSubgroup η.hom hle
  -- The projection to the quotient by `U` factors through the `m`-th coordinate of `A(L)`: both
  -- sides are continuous into a discrete space and agree on the dense image of `Lˣ`.
  have hfac : ∀ d, QuotientGroup.mk' U.toSubgroup d =
      e ((profiniteCompletionToPadicCompletionUnits p L d).1 m) := by
    refine congrFun <| (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Lˣ)).equalizer
      QuotientGroup.continuous_mk (continuous_of_discreteTopology.comp <|
        (continuous_apply m).comp <| continuous_subtype_val.comp
          (profiniteCompletionToPadicCompletionUnits p L).continuous) (funext fun a ↦ ?_)
    simp only [Function.comp_apply, profiniteCompletionToPadicCompletionUnits_etaFn,
      padicCompletionUnitsOf_apply, QuotientGroup.mk'_apply, e, QuotientGroup.map_mk]
    -- Mathlib's `eta` is `etaFn` bundled as a homomorphism, by definition, with no `simp` lemma.
    rfl
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, hfac, hc]
  exact map_one e

/-- The maximal pro-`p` quotient of the profinite completion of `Lˣ` is canonically the
inverse-limit completion `A(L) = lim_m Lˣ/(Lˣ)^(p^m)`. -/
def maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits :
    maximalProPQuotient p (ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Lˣ)) ≃ₜ*
      ↑(padicCompletionUnits p L) :=
  let F := profiniteCompletionToPadicCompletionUnits p L
  let f := maximalProPQuotient.lift (isProP_padicCompletionUnits p L) F.toMonoidHom F.continuous
  have hf : Continuous f := maximalProPQuotient.continuous_lift _ _ F.continuous
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).2 fun x hx ↦ ?_
    obtain ⟨c, rfl⟩ := maximalProPQuotient.mk_surjective p _ x
    exact (QuotientGroup.eq_one_iff c).2
      (mem_proPKernel_of_profiniteCompletionToPadicCompletionUnits_eq_one p L
        ((maximalProPQuotient.lift_mk _ _ _ c).symm.trans hx))
  have hsurj : Function.Surjective f := fun y ↦ by
    obtain ⟨c, rfl⟩ := surjective_profiniteCompletionToPadicCompletionUnits p L y
    exact ⟨maximalProPQuotient.mk p _ c, maximalProPQuotient.lift_mk _ _ _ c⟩
  let e := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  { e with
    continuous_toFun := hf
    continuous_invFun := hf.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

/-- The canonical comparison sends the class of a unit to its compatible family of power
classes. -/
@[simp]
theorem maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits_mk (x : Lˣ) :
    maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits p L
        (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Lˣ) x : maximalProPQuotient p _) =
      padicCompletionUnitsOf p L x :=
  (maximalProPQuotient.lift_mk _ _ _ _).trans
    (profiniteCompletionToPadicCompletionUnits_etaFn p L x)

/-- The inverse comparison sends the compatible family of power classes of a unit to the class
of that unit. -/
@[simp]
theorem maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits_symm_apply (x : Lˣ) :
    (maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits p L).symm
        (padicCompletionUnitsOf p L x) =
      (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Lˣ) x : maximalProPQuotient p _) := by
  rw [ContinuousMulEquiv.symm_apply_eq,
    maximalProPQuotientProfiniteCompletionEquivPadicCompletionUnits_mk]

end TauCeti
