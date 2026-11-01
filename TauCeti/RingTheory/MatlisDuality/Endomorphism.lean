/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.QuotientLinearMap
public import TauCeti.Algebra.Module.Torsion.ResidueField
public import TauCeti.RingTheory.AdicCompletion.Torsion
public import TauCeti.RingTheory.Length
public import TauCeti.RingTheory.MatlisDuality.FiniteLength

/-!
# The endomorphisms of the injective hull of the residue field

Let `R` be a Noetherian local ring with maximal ideal `𝔪` and residue field `κ`, and let
`ι : κ → E` be an injective envelope of `κ`. Every element of `E` is killed by a power of `𝔪`, so
the `𝔪`-adic completion `R̂` acts on `E` (`TauCeti.AdicCompletion.torsionModule`). This file proves
that this action identifies `R̂` with the ring of `R`-linear endomorphisms of `E`: in Matlis duality
notation, `D(E) = Hom_R(E, E) ≅ R̂`. Neither completeness of `R` nor finiteness of `κ` is assumed.

The identification is assembled from the layers `E[𝔪ⁿ]` of elements killed by `𝔪ⁿ`. Each layer
is the Matlis dual `Hom_R(R ⧸ 𝔪ⁿ, E)` of a module of finite length, so finite-length biduality makes
every linear map `E[𝔪ⁿ] → E` a multiplication by a scalar, and that scalar is determined modulo
`𝔪ⁿ`, because the annihilator of `E[J]` is `J` for every ideal `J`. An endomorphism of `E` is
therefore a compatible system of residues modulo `𝔪ⁿ`, that is, an element of `R̂`.

## Main declarations

* `TauCeti.annihilator_torsionBySet_of_injective`: if `E` is injective and contains a copy of
  `κ`, then the annihilator of `E[J]` is `J`, for every ideal `J`.
* `TauCeti.IsInjectiveEnvelope.exists_eq_smul_subtype`: for an ideal `J` with `R ⧸ J` of finite
  length, every linear map `E[J] → E` is the inclusion multiplied by a scalar.
* `TauCeti.IsInjectiveEnvelope.adicCompletionEquivEnd`: the `R`-algebra isomorphism
  `R̂ ≃ End_R(E)` given by the completion action, with `adicCompletionEquivEnd_apply_of_mem` and
  `evalₐ_adicCompletionEquivEnd_symm` computing it and its inverse through residues modulo `𝔪ⁿ`.

## References

* The Stacks Project, Section 47.7, Matlis duality, Tag 08Z1, and Lemma 47.7.5, Tag 08Z6.
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

namespace TauCeti

open IsLocalRing Submodule

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R] {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E}

/-- If `E` is injective and contains a copy of the residue field, then the elements of `E`
killed by an ideal `J` have annihilator exactly `J`. -/
theorem annihilator_torsionBySet_of_injective [Small.{v} R] [Module.Injective R E]
    (hι : Function.Injective ι) (J : Ideal R) : (torsionBySet R E J).annihilator = J := by
  refine le_antisymm (fun r hr => ?_) fun r hr => mem_annihilator.mpr fun x hx =>
    (mem_torsionBySet_iff _ _).mp hx ⟨r, hr⟩
  -- `E` cogenerates `R ⧸ J`, so the class of `r` is detected by a map `R ⧸ J → E`; that map
  -- sends `1` into `E[J]`, which `r` kills.
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine (injective_iff_map_eq_zero _).mp
    (injective_applyₗ_of_injective (M := R ⧸ J) hι) _ (LinearMap.ext fun f => ?_)
  simpa [f.apply_quotient_mk_eq_smul_apply_one] using
    mem_annihilator.mp hr _ (J.quotientLinearMapEquivTorsionBySet E f).prop

/-- **Linear maps out of a layer of the hull are scalar.** Let `E` be an injective envelope of the
residue field and `J` an ideal with `R ⧸ J` of finite length. Every linear map `E[J] → E` is the
inclusion multiplied by a scalar. -/
theorem IsInjectiveEnvelope.exists_eq_smul_subtype [Small.{v} R] (hι : IsInjectiveEnvelope ι)
    {J : Ideal R} (hJ : IsFiniteLength R (R ⧸ J)) (g : torsionBySet R E J →ₗ[R] E) :
    ∃ r : R, g = r • (torsionBySet R E J).subtype := by
  -- `E[J]` is the Matlis dual of `R ⧸ J` through evaluation at `1`, and the composite of `g` with
  -- this identification is evaluation at some class `[r]`, by finite-length biduality.
  obtain ⟨m, hm⟩ := (hι.bijective_applyₗ hJ).2
    (g ∘ₗ (J.quotientLinearMapEquivTorsionBySet E).toLinearMap)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  refine ⟨r, LinearMap.ext fun x => ?_⟩
  simpa using (LinearMap.congr_fun hm ((J.quotientLinearMapEquivTorsionBySet E).symm x)).symm

variable [IsNoetherianRing R]

namespace IsInjectiveEnvelope

/-- Every element of an injective envelope of the residue field is killed by a power of `𝔪`. -/
private theorem mem_primaryComponent (hι : IsInjectiveEnvelope ι) (x : E) :
    x ∈ (maximalIdeal R).primaryComponent E :=
  hι.isEssential_range.primaryComponent_maximalIdeal_eq_top ▸ mem_top

/-- The completion action on an injective envelope of the residue field, as an algebra map into
the endomorphisms. -/
private def toEnd (hι : IsInjectiveEnvelope ι) :
    AdicCompletion (maximalIdeal R) R →ₐ[R] Module.End R E :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  haveI := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  Algebra.lsmul R R E

private theorem toEnd_apply (hι : IsInjectiveEnvelope ι) (a : AdicCompletion (maximalIdeal R) R)
    {x : E} {n : ℕ} (hx : x ∈ torsionBySet R E ↑(maximalIdeal R ^ n)) {r : R}
    (ha : AdicCompletion.evalₐ (maximalIdeal R) n a = Ideal.Quotient.mk _ r) :
    toEnd hι a x = r • x :=
  a.torsion_smul_eq _ x r hx ha

private theorem toEnd_injective [Small.{v} R] (hι : IsInjectiveEnvelope ι) :
    Function.Injective (toEnd hι) := by
  have := hι.moduleInjective
  refine (injective_iff_map_eq_zero _).mpr fun a ha => AdicCompletion.ext_evalₐ fun n => ?_
  -- A residue of `a` modulo `𝔪ⁿ` kills `E[𝔪ⁿ]`, so it lies in `𝔪ⁿ`.
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) n a)
  rw [map_zero, ← hr, Ideal.Quotient.eq_zero_iff_mem,
    ← annihilator_torsionBySet_of_injective hι.injective (maximalIdeal R ^ n)]
  exact mem_annihilator.mpr fun x hx => by
    rw [← toEnd_apply hι a hx hr.symm, ha, LinearMap.zero_apply]

private theorem toEnd_surjective [Small.{v} R] (hι : IsInjectiveEnvelope ι) :
    Function.Surjective (toEnd hι) := by
  have := hι.moduleInjective
  intro φ
  -- On `E[𝔪ⁿ]` the endomorphism `φ` is multiplication by some `r n`.
  choose r hr using fun n => hι.exists_eq_smul_subtype
    (isFiniteLength_quotient_maximalIdeal_pow n)
    (φ ∘ₗ (torsionBySet R E ↑(maximalIdeal R ^ n)).subtype)
  have hφ (n : ℕ) {x : E} (hx : x ∈ torsionBySet R E ↑(maximalIdeal R ^ n)) : φ x = r n • x := by
    simpa using LinearMap.congr_fun (hr n) ⟨x, hx⟩
  -- The scalars `r n` form an adic Cauchy sequence, since `r m - r n` kills `E[𝔪ᵐ]` for `m ≤ n`.
  have hcauchy : AdicCompletion.IsAdicCauchy (maximalIdeal R) R r := fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
      ← annihilator_torsionBySet_of_injective hι.injective (maximalIdeal R ^ m)]
    refine mem_annihilator.mpr fun x hx => ?_
    rw [sub_smul, ← hφ m hx,
      ← hφ n (torsionBySet_le_torsionBySet_pow _ _ hmn (maximalIdeal R) hx), sub_self]
  refine ⟨AdicCompletion.mkₐ (maximalIdeal R) ⟨r, @hcauchy⟩, LinearMap.ext fun x => ?_⟩
  obtain ⟨n, hn⟩ := ((maximalIdeal R).primaryComponent_mem E x).mp (hι.mem_primaryComponent x)
  rw [toEnd_apply hι _ hn (AdicCompletion.evalₐ_mkₐ _ n ⟨r, @hcauchy⟩), hφ n hn]

variable [Small.{v} R]

/-- **The endomorphisms of the injective hull of the residue field are the completion.** For an
injective envelope `E` of the residue field of a Noetherian local ring `R`, the action of the
`𝔪`-adic completion on `E` is an isomorphism of `R`-algebras `R̂ ≃ End_R(E)`. In Matlis duality
notation, `D(E) = Hom_R(E, E) ≅ R̂`. -/
def adicCompletionEquivEnd (hι : IsInjectiveEnvelope ι) :
    AdicCompletion (maximalIdeal R) R ≃ₐ[R] Module.End R E :=
  AlgEquiv.ofBijective (toEnd hι) ⟨toEnd_injective hι, toEnd_surjective hι⟩

/-- A completed scalar acts on an element killed by `𝔪ⁿ` through any representative of its
residue modulo `𝔪ⁿ`. -/
theorem adicCompletionEquivEnd_apply_of_mem (hι : IsInjectiveEnvelope ι)
    (a : AdicCompletion (maximalIdeal R) R) {x : E} {n : ℕ}
    (hx : x ∈ torsionBySet R E ↑(maximalIdeal R ^ n)) {r : R}
    (ha : AdicCompletion.evalₐ (maximalIdeal R) n a = Ideal.Quotient.mk _ r) :
    hι.adicCompletionEquivEnd a x = r • x :=
  toEnd_apply hι a hx ha

/-- The isomorphism is the canonical completion action on the `𝔪`-power-torsion module `E`. -/
theorem adicCompletionEquivEnd_apply (hι : IsInjectiveEnvelope ι)
    (hM : ∀ x : E, x ∈ (maximalIdeal R).primaryComponent E)
    (a : AdicCompletion (maximalIdeal R) R) (x : E) :
    letI := AdicCompletion.torsionModule hM
    hι.adicCompletionEquivEnd a x = a • x := by
  obtain ⟨n, hn⟩ := ((maximalIdeal R).primaryComponent_mem E x).mp (hM x)
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal R) n a)
  rw [hι.adicCompletionEquivEnd_apply_of_mem a hn hr.symm, a.torsion_smul_eq hM x r hn hr.symm]

/-- The image of an element of `R` acts by its scalar multiplication. -/
@[simp]
theorem adicCompletionEquivEnd_of (hι : IsInjectiveEnvelope ι) (r : R) (x : E) :
    hι.adicCompletionEquivEnd (AdicCompletion.of (maximalIdeal R) R r) x = r • x := by
  obtain ⟨n, hn⟩ := ((maximalIdeal R).primaryComponent_mem E x).mp (hι.mem_primaryComponent x)
  exact hι.adicCompletionEquivEnd_apply_of_mem _ hn (AdicCompletion.evalₐ_of _ n r)

/-- The completed scalar of an endomorphism `φ` has residue `[r]` modulo `𝔪ⁿ` whenever `φ` is
multiplication by `r` on the elements killed by `𝔪ⁿ`. -/
theorem evalₐ_adicCompletionEquivEnd_symm (hι : IsInjectiveEnvelope ι) (φ : Module.End R E)
    {n : ℕ} {r : R} (hφ : ∀ x ∈ torsionBySet R E ↑(maximalIdeal R ^ n), φ x = r • x) :
    AdicCompletion.evalₐ (maximalIdeal R) n (hι.adicCompletionEquivEnd.symm φ) =
      Ideal.Quotient.mk _ r := by
  have := hι.moduleInjective
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal R) n (hι.adicCompletionEquivEnd.symm φ))
  rw [← hs, Ideal.Quotient.eq,
    ← annihilator_torsionBySet_of_injective hι.injective (maximalIdeal R ^ n)]
  refine mem_annihilator.mpr fun x hx => ?_
  rw [sub_smul, ← hι.adicCompletionEquivEnd_apply_of_mem _ hx hs.symm,
    AlgEquiv.apply_symm_apply, hφ x hx, sub_self]

end IsInjectiveEnvelope

end TauCeti
