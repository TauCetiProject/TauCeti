/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.RingTheory.Perfectoid.PrimitiveUntilt.Basic
public import TauCeti.RingTheory.WittVector.Primitive.Quotient

import Mathlib.Algebra.CharP.Subring
import TauCeti.RingTheory.Huber.Pair.Complete

/-!
# Functoriality, quotients, and `p`-recovery of untilts

This file develops the morphisms attached to the untilt `untilt p P J` of a Huber pair
`P = (R, R⁺)` along an ideal `J ⊆ 𝕎 R⁺`:

* **Functoriality** `untilt.map` sends a ring homomorphism `f : R →+* S` carrying `P.plus` into
  `Q.plus` with `J ≤ J'.comap (WittVector.map f⁺)` to a ring homomorphism
  `untilt p P J →+* untilt p Q J'` compatible with `algebraMap` (`untilt.map_algebraMap`),
  `sharpPlus` (`untilt.map_sharpPlus`), and `sharp` (`untilt.map_sharp`), and preserving
  `untiltPlus` (`untilt.map_mem_untiltPlus`). No primitivity assumption on `J` or `J'` is needed;
  when `R` and `S` are Tate rings and `f` is continuous, `untilt.map` is continuous
  (`untilt.continuous_map`).
* **Quotients along a primitive element** `ξ`: convenience lemmas for `untilt.quotientSharpEquiv`
  and `untilt.quotientEquivUntiltPlus` on sharp images.
* **Recovery along `(p)`**: for a perfect Tate ring `R` of characteristic `p`,
  `untilt.spanPEquivSelf` specialises `untilt.spanPEquiv` to `untilt p P (span {p}) ≃+* R` whose
  inverse is `untilt.sharp`, identifies `untiltPlus` with `R⁺`, and is a homeomorphism whenever
  `R` is uniform (`untilt.isHomeomorph_spanPEquivSelf`).

## Main definitions

* `TauCeti.Perfectoid.untilt.map`: functoriality `untilt p P J →+* untilt p Q J'`.
* `TauCeti.Perfectoid.untilt.spanPEquivSelf`: `untilt p P (span {p}) ≃+* R`.

## Main results

* `TauCeti.Perfectoid.untilt.map_algebraMap`, `TauCeti.Perfectoid.untilt.map_sharpPlus`,
  `TauCeti.Perfectoid.untilt.map_sharp`, `TauCeti.Perfectoid.untilt.map_id`,
  `TauCeti.Perfectoid.untilt.map_comp`, `TauCeti.Perfectoid.untilt.continuous_map`.
* `TauCeti.Perfectoid.untilt.quotientEquivUntiltPlus_mk_teichmuller`,
  `TauCeti.Perfectoid.untilt.quotientSharpEquiv_symm_mk`.
* `TauCeti.Perfectoid.untilt.spanPEquivSelf_algebraMap`,
  `TauCeti.Perfectoid.untilt.spanPEquivSelf_symm_apply`,
  `TauCeti.Perfectoid.untilt.spanPEquivSelf_sharp`,
  `TauCeti.Perfectoid.untilt.mem_untiltPlus_iff_spanPEquivSelf_mem`,
  `TauCeti.Perfectoid.untilt.isHomeomorph_spanPEquivSelf`.

## References

* P. Scholze, *Étale cohomology of diamonds*, Theorem 3.17 and its proof.
* P. Scholze and J. Weinstein, *Berkeley lectures on `p`-adic geometry*, Theorem 6.2.11.
* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, Theorem 2.3.9.
-/

public section

open Filter Topology TauCeti.Huber WittVector

namespace TauCeti.Perfectoid.untilt

/-! ### Functoriality -/

section Map

variable {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [IsHuberRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [IsHuberRing S] {P : Pair R} {Q : Pair S} {J : Ideal (WittVector p P.plus)}
  {J' : Ideal (WittVector p Q.plus)}

/-- **Functoriality of the untilt**: a ring homomorphism `f : R →+* S` carrying `P.plus` into
`Q.plus` with `J ≤ J'.comap (WittVector.map f⁺)` induces a ring homomorphism
`untilt p P J →+* untilt p Q J'`, for arbitrary ideals `J` and `J'`. -/
noncomputable def map (f : R →+* S) (hfplus : ∀ x ∈ P.plus, f x ∈ Q.plus)
    (hJ : J ≤ J'.comap (WittVector.map (f.restrict P.plus Q.plus hfplus))) :
    untilt p P J →+* untilt p Q J' :=
  let g : WittVector p P.plus ⧸ J →+* WittVector p Q.plus ⧸ J' :=
    Ideal.Quotient.lift J ((Ideal.Quotient.mk J').comp (WittVector.map (f.restrict _ _ hfplus)))
      fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (hJ ha)
  IsLocalization.lift (M := (untiltDenominators p P).map (Ideal.Quotient.mk J))
    (g := (algebraMap (WittVector p Q.plus ⧸ J') (untilt p Q J')).comp g) <| by
    rintro ⟨_, _, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := mem_untiltDenominators.mp hx
    dsimp only [RingHom.comp_apply, g]
    rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, map_teichmuller]
    exact IsLocalization.map_units (untilt p Q J')
      ⟨Ideal.Quotient.mk J' (teichmuller p (f.restrict P.plus Q.plus hfplus a)),
        Submonoid.mem_map_of_mem _ (mem_untiltDenominators.mpr
          ⟨f.restrict P.plus Q.plus hfplus a, ha.map f, rfl⟩)⟩

/-- `untilt.map` commutes with the canonical map from `𝕎 R⁺`. -/
@[simp]
theorem map_algebraMap (f : R →+* S) (hfplus : ∀ x ∈ P.plus, f x ∈ Q.plus)
    (hJ : J ≤ J'.comap (WittVector.map (f.restrict P.plus Q.plus hfplus)))
    (w : WittVector p P.plus) :
    map f hfplus hJ (algebraMap (WittVector p P.plus ⧸ J) (untilt p P J) (Ideal.Quotient.mk J w)) =
      algebraMap (WittVector p Q.plus ⧸ J') (untilt p Q J')
        (Ideal.Quotient.mk J' (WittVector.map (f.restrict P.plus Q.plus hfplus) w)) := by
  simp [map]

/-- `untilt.map` carries `untiltPlus` into `untiltPlus`. -/
theorem map_mem_untiltPlus (f : R →+* S) (hfplus : ∀ x ∈ P.plus, f x ∈ Q.plus)
    (hJ : J ≤ J'.comap (WittVector.map (f.restrict P.plus Q.plus hfplus)))
    {x : untilt p P J} (hx : x ∈ untiltPlus p P J) :
    map f hfplus hJ x ∈ untiltPlus p Q J' := by
  obtain ⟨a, rfl⟩ := mem_untiltPlus.mp hx
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [map_algebraMap]
  exact mem_untiltPlus.mpr ⟨_, rfl⟩

/-- `untilt.map` intertwines the sharp maps on `P.plus`. -/
@[simp]
theorem map_sharpPlus (f : R →+* S) (hfplus : ∀ x ∈ P.plus, f x ∈ Q.plus)
    (hJ : J ≤ J'.comap (WittVector.map (f.restrict P.plus Q.plus hfplus))) (a : P.plus) :
    map f hfplus hJ (sharpPlus p P J a) =
      sharpPlus p Q J' (f.restrict P.plus Q.plus hfplus a) := by
  rw [sharpPlus_apply, sharpPlus_apply, algebraMap_apply, algebraMap_apply, map_algebraMap,
    map_teichmuller]

/-- `untilt.map` is the identity on the identity ring homomorphism. -/
@[simp]
theorem map_id (hJ : J ≤ J.comap (WittVector.map ((RingHom.id R).restrict P.plus P.plus
    fun _ hx ↦ hx))) :
    map (RingHom.id R) (fun _ hx ↦ hx) hJ = RingHom.id (untilt p P J) := by
  apply IsLocalization.ringHom_ext ((untiltDenominators p P).map (Ideal.Quotient.mk J))
  ext w
  simp only [RingHom.comp_apply, RingHom.id_apply, map_algebraMap]
  have hid : (RingHom.id R).restrict P.plus P.plus (fun _ hx ↦ hx) = RingHom.id P.plus := rfl
  rw [hid, WittVector.map_id, RingHom.id_apply]

/-- `untilt.map` respects composition of ring homomorphisms. -/
theorem map_comp {T : Type*} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [IsHuberRing T] {P' : Pair T} {J'' : Ideal (WittVector p P'.plus)}
    (f : R →+* S) (hfplus : ∀ x ∈ P.plus, f x ∈ Q.plus)
    (hJ : J ≤ J'.comap (WittVector.map (f.restrict P.plus Q.plus hfplus)))
    (g : S →+* T) (hgplus : ∀ x ∈ Q.plus, g x ∈ P'.plus)
    (hJ' : J' ≤ J''.comap (WittVector.map (g.restrict Q.plus P'.plus hgplus))) :
    (map g hgplus hJ').comp (map f hfplus hJ) =
      map (g.comp f) (fun _ hx ↦ hgplus _ (hfplus _ hx)) (fun w hw ↦ by
        have hcomp : WittVector.map (p := p) ((g.comp f).restrict P.plus P'.plus
            fun _ hx ↦ hgplus _ (hfplus _ hx)) =
            (WittVector.map (g.restrict Q.plus P'.plus hgplus)).comp
              (WittVector.map (f.restrict P.plus Q.plus hfplus)) := by
          ext n
          simp
        rw [Ideal.mem_comap, hcomp, RingHom.comp_apply]
        exact hJ' (hJ hw)) := by
  apply IsLocalization.ringHom_ext ((untiltDenominators p P).map (Ideal.Quotient.mk J))
  ext w
  simp only [RingHom.comp_apply, map_algebraMap]
  congr 2

end Map

section TateMap

variable {p : ℕ} [Fact p.Prime] {R S : Type*} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [IsTateRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
  [IsTateRing S] {P : Pair R} {Q : Pair S} {J : Ideal (WittVector p P.plus)}
  {J' : Ideal (WittVector p Q.plus)}

/-- `untilt.map` intertwines `sharp` on `R`. -/
@[simp]
theorem map_sharp (f : R →+* S) (hfplus : ∀ x ∈ P.plus, f x ∈ Q.plus)
    (hJ : J ≤ J'.comap (WittVector.map (f.restrict P.plus Q.plus hfplus))) (x : R) :
    map f hfplus hJ (sharp p P J x) = sharp p Q J' (f x) := by
  have := P.isRingOfIntegralElements.isLocalization
  have heq : (map f hfplus hJ).toMonoidHom.comp (sharp p P J).toMonoidHom =
      (sharp p Q J').toMonoidHom.comp f.toMonoidHom :=
    (IsLocalization.toLocalizationMap ((IsUnit.submonoid R).comap P.plus.subtype)
      R).epic_of_localizationMap <| MonoidHom.ext fun a ↦ by
      dsimp
      rw [Algebra.algebraMap_ofSubsemiring_apply, sharp_coe, map_sharpPlus, ← sharp_coe]
      rfl
  exact DFunLike.congr_fun heq x

/-- **Continuity of `untilt.map`**: for a continuous plus-preserving ring homomorphism between
Tate rings with `J ≤ J'.comap (𝕎 f⁺)`, the induced map on untilts is continuous, for arbitrary
ideals `J` and `J'`. -/
theorem continuous_map (f : R →+* S) (hf : Continuous f) (hfplus : ∀ x ∈ P.plus, f x ∈ Q.plus)
    (hJ : J ≤ J'.comap (WittVector.map (f.restrict P.plus Q.plus hfplus))) :
    Continuous (map f hfplus hJ) := by
  refine continuous_of_continuousAt_zero (map f hfplus hJ : untilt p P J →+ untilt p Q J') ?_
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  have hϖ' : IsPseudoUniformizer ((f.restrict P.plus Q.plus hfplus ϖ : Q.plus) : S) :=
    hϖ.map hf
  rw [ContinuousAt, map_zero,
    (hasBasis_nhds_zero (J := J) hϖ).tendsto_iff (hasBasis_nhds_zero (J := J') hϖ')]
  refine fun n _ ↦ ⟨n, trivial, fun x hx ↦ ?_⟩
  obtain ⟨a, rfl⟩ := mem_awayNhd.mp hx
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine mem_awayNhd.mpr ⟨Ideal.Quotient.mk J' (WittVector.map (f.restrict _ _ hfplus) w), ?_⟩
  symm
  simp only [AddMonoidHom.coe_ofClass, map_mul, map_pow, map_algebraMap, map_teichmuller]

end TateMap

/-! ### Quotients along a primitive element -/

section Quotient

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [IsTateRing R] [CharP R p] [PerfectRing R p] {P : Pair R}
  {ξ : WittVector p P.plus}

/-- `quotientEquivUntiltPlus` carries the class of `[a]` to `sharp a`. -/
@[simp]
theorem quotientEquivUntiltPlus_mk_teichmuller (hξ : ξ.IsPrimitive) (a : P.plus) :
    quotientEquivUntiltPlus hξ (Ideal.Quotient.mk (Ideal.span {ξ}) (teichmuller p a)) =
      ⟨sharp p P (Ideal.span {ξ}) a, sharp_mem_untiltPlus a⟩ :=
  Subtype.ext ((coe_quotientEquivUntiltPlus_apply hξ _).trans (sharp_apply a).symm)

/-- The inverse of `quotientSharpEquiv` sends the class of `a` to the class of `sharp a`. -/
@[simp]
theorem quotientSharpEquiv_symm_mk (hξ : ξ.IsPrimitive) {ϖ : P.plus} (hξ₀ : ϖ ∣ ξ.coeff 0)
    (a : P.plus) :
    (quotientSharpEquiv hξ hξ₀).symm (Ideal.Quotient.mk (Ideal.span {ϖ}) a) =
      Ideal.Quotient.mk _ ⟨sharp p P (Ideal.span {ξ}) a, sharp_mem_untiltPlus a⟩ := by
  rw [RingEquiv.symm_apply_eq, quotientSharpEquiv_mk_sharp]

end Quotient

/-! ### Recovery along `(p)` -/

section SpanPEquivSelf

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R] [IsTateRing R] [CharP R p] [PerfectRing R p] (P : Pair R)

/-- **Recovery of `R` from the untilt along `(p)`**: for a perfect Tate ring `R` of characteristic
`p`, `untilt p P (Ideal.span {p}) ≃+* R` as rings, specialising `untilt.spanPEquiv`. -/
noncomputable def spanPEquivSelf :
    untilt p P (Ideal.span {(p : WittVector p P.plus)}) ≃+* R :=
  let hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  letI := P.plus.isLocalizationAway_of_isOpen P.isRingOfIntegralElements.isOpen _
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  spanPEquiv hϖ R

/-- `spanPEquivSelf` sends the class of a Witt vector `w` to its zeroth coordinate. -/
@[simp]
theorem spanPEquivSelf_algebraMap (w : WittVector p P.plus) :
    spanPEquivSelf p P (algebraMap (WittVector p P.plus ⧸ Ideal.span {(p : WittVector p P.plus)})
      (untilt p P (Ideal.span {(p : WittVector p P.plus)})) (Ideal.Quotient.mk _ w)) =
      (w.coeff 0 : R) := by
  have hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  have := P.plus.isLocalizationAway_of_isOpen P.isRingOfIntegralElements.isOpen _
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  rw [← algebraMap_apply]
  exact spanPEquiv_algebraMap hϖ R w

/-- The inverse of `spanPEquivSelf` is `sharp` along `(p)`. -/
@[simp]
theorem spanPEquivSelf_symm_apply (x : R) :
    (spanPEquivSelf p P).symm x = sharp p P (Ideal.span {(p : WittVector p P.plus)}) x := by
  have hϖ := P.isRingOfIntegralElements.exists_isPseudoUniformizer.choose_spec
  have := P.plus.isLocalizationAway_of_isOpen P.isRingOfIntegralElements.isOpen _
    hϖ.isTopologicallyNilpotent hϖ.isUnit
  let f : R →* untilt p P (Ideal.span {(p : WittVector p P.plus)}) := (spanPEquivSelf p P).symm
  have heq : f = (sharp p P (Ideal.span {(p : WittVector p P.plus)}) : R →* _) :=
    sharp_unique fun a ↦ by
      dsimp only [f, spanPEquivSelf]
      rw [MonoidHom.coe_ofClass,
        ← Algebra.algebraMap_ofSubsemiring_apply (S := P.plus) (R := R) a]
      exact (spanPEquiv_symm_algebraMap hϖ R a).trans (by rw [sharpPlus_apply, algebraMap_apply])
  exact DFunLike.congr_fun heq x

/-- `spanPEquivSelf` is left-inverse to `sharp`. -/
@[simp]
theorem spanPEquivSelf_sharp (x : R) :
    spanPEquivSelf p P (sharp p P (Ideal.span {(p : WittVector p P.plus)}) x) = x := by
  rw [← spanPEquivSelf_symm_apply, RingEquiv.apply_symm_apply]

/-- Under `spanPEquivSelf`, `untiltPlus` corresponds to `P.plus`. -/
theorem mem_untiltPlus_iff_spanPEquivSelf_mem
    {x : untilt p P (Ideal.span {(p : WittVector p P.plus)})} :
    x ∈ untiltPlus p P (Ideal.span {(p : WittVector p P.plus)}) ↔
      spanPEquivSelf p P x ∈ P.plus := by
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := mem_untiltPlus.mp hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [spanPEquivSelf_algebraMap]
    exact (w.coeff 0).property
  · intro hx
    have hsymm := (spanPEquivSelf p P).symm_apply_apply x
    rw [spanPEquivSelf_symm_apply] at hsymm
    rw [← hsymm]
    exact (sharp_coe (J := Ideal.span {(p : WittVector p P.plus)})
      ⟨spanPEquivSelf p P x, hx⟩).symm ▸
      sharpPlus_mem_untiltPlus (J := Ideal.span {(p : WittVector p P.plus)})
        ⟨spanPEquivSelf p P x, hx⟩

/-- **`spanPEquivSelf` is a homeomorphism** whenever `R` is uniform (in particular whenever `R`
is a perfect complete Hausdorff Tate ring of characteristic `p`). -/
theorem isHomeomorph_spanPEquivSelf [IsUniform R] : IsHomeomorph (spanPEquivSelf p P) := by
  obtain ⟨ϖ, hϖ⟩ := P.isRingOfIntegralElements.exists_isPseudoUniformizer
  let D : PairOfDefinition R := PairOfDefinition.ofIsPseudoUniformizer P.plus
    P.isRingOfIntegralElements.isOpen P.isRingOfIntegralElements.isBounded hϖ ϖ.property
  have hbasis_A := hasBasis_nhds_zero (J := Ideal.span {(p : WittVector p P.plus)}) hϖ
  have hcont_symm : Continuous (spanPEquivSelf p P).symm := by
    have heq : ⇑(spanPEquivSelf p P).symm = ⇑(sharp p P (Ideal.span {(p : WittVector p P.plus)})) :=
      funext (spanPEquivSelf_symm_apply p P)
    rw [heq]
    exact continuous_sharp WittVector.isPrimitive_p
  have hcont : Continuous (spanPEquivSelf p P) := by
    refine continuous_of_continuousAt_zero
      (spanPEquivSelf p P : untilt p P (Ideal.span {(p : WittVector p P.plus)}) →+ R) ?_
    rw [ContinuousAt, map_zero, hbasis_A.tendsto_iff (hϖ.hasBasis_nhds_zero D)]
    refine fun n _ ↦ ⟨n, trivial, fun x hx ↦ ?_⟩
    obtain ⟨a, rfl⟩ := mem_awayNhd.mp hx
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective a
    simp only [AddMonoidHom.coe_ofClass, map_mul, map_pow, spanPEquivSelf_algebraMap,
      teichmuller_coeff_zero]
    refine ⟨(w.coeff 0 : R), ?_, rfl⟩
    rw [PairOfDefinition.ofIsPseudoUniformizer_ringOfDefinition]
    exact (w.coeff 0).property
  exact (Homeomorph.mk (spanPEquivSelf p P).toEquiv hcont hcont_symm).isHomeomorph

end SpanPEquivSelf

end TauCeti.Perfectoid.untilt
