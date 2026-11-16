/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import TauCeti.Algebra.Module.SpanRank
import TauCeti.RingTheory.RegularLocalRing.CohenMacaulay
import TauCeti.RingTheory.RegularLocalRing.MiracleFlatness
import TauCeti.RingTheory.RegularLocalRing.Quotient
import TauCeti.RingTheory.RegularLocalRing.Smooth

/-!
# Regular local algebras with a retraction to the base

Let `R` and `A` be regular local rings and let `A` be an `R`-algebra with an `R`-algebra
retraction `g : A →ₐ[R] R`. Geometrically, `A` is the local ring of a scheme over `Spec R` at
a point through which a section passes, and both the scheme and the base are regular there.

The closed fibre `A ⧸ 𝔪_R A` is then again a regular local ring and
`dim A = dim R + dim (A ⧸ 𝔪_R A)`. Indeed, the kernel of `g` is cut out by part of a regular system
of parameters of `A`, because its quotient `R` is regular. The remaining parameters are carried by
`g` onto generators of `𝔪_R`, so at least `dim R` of them remain. As `𝔪_A` is the sum of `𝔪_R A`
and the kernel of `g`, the closed fibre has embedding dimension at most `dim A - dim R`, which
Krull's height theorem bounds by its dimension.

By miracle flatness `A` is flat over `R`. If `A` is moreover essentially of finite presentation
over `R`, it is formally smooth over `R`: the closed fibre is a regular local ring, essentially of
finite type over the residue field `k` of `R`, whose residue field is `k` itself, so it is formally
smooth over `k`, and a flat local algebra with formally smooth closed fibre is formally smooth.

So no flatness hypothesis is needed: a section of a morphism locally of finite presentation
through a point at which both the source and the base are regular lands in the smooth locus
(`AlgebraicGeometry.Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing`).

## Main results

* `AlgHom.isLocalHom_algebraMap`: the structure map `R → A` is local.
* `AlgHom.maximalIdeal_le_map_sup_ker`: `𝔪_A` is contained in `𝔪_R A + ker g`, for local rings
  `R` and `A`.
* `AlgHom.isRegularLocalRing_quotient_map_maximalIdeal`: the closed fibre is regular.
* `AlgHom.ringKrullDim_eq_add_ringKrullDim_quotient`: `dim A = dim R + dim (A ⧸ 𝔪_R A)`.
* `AlgHom.flat_of_isRegularLocalRing`: `A` is flat over `R`.
* `AlgHom.formallySmooth_of_isRegularLocalRing`: `A` is formally smooth over `R` when it is
  essentially of finite presentation.
* `Algebra.IsSmoothAt.of_isRegularLocalRing`: the same at a prime of a finitely presented algebra,
  phrased with a left inverse of the map of localizations `R_p → S_q`.

## References

* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 9.1 (sections of regular fibred
  surfaces pass through the smooth locus).
* [The Stacks Project, Lemma 10.106.4](https://stacks.math.columbia.edu/tag/00NR) (regular
  quotients are cut out by parameters).
* [The Stacks Project, Lemma 10.128.1](https://stacks.math.columbia.edu/tag/00R4) (miracle
  flatness).
* [The Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF) (flat with
  smooth fibre is smooth).
-/

public section

open IsLocalRing Ideal TensorProduct

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The structure map of an algebra with a retraction is a local homomorphism. -/
theorem isLocalHom_algebraMap (g : A →ₐ[R] R) : IsLocalHom (algebraMap R A) := by
  have : (g : A →+* R).comp (algebraMap R A) = RingHom.id R := by ext; simp
  have : IsLocalHom ((g : A →+* R).comp (algebraMap R A)) := by rw [this]; infer_instance
  exact isLocalHom_of_comp _ (g : A →+* R)

section IsLocalRing

variable [IsLocalRing R] [IsLocalRing A]

/-- The maximal ideal of `A` is the sum of the extension of the maximal ideal of `R` and the
kernel of the retraction. -/
theorem maximalIdeal_le_map_sup_ker (g : A →ₐ[R] R) :
    maximalIdeal A ≤ (maximalIdeal R).map (algebraMap R A) ⊔ RingHom.ker g := by
  have : IsLocalHom (g : A →+* R) :=
    .of_surjective _ fun r ↦ ⟨algebraMap R A r, by simp⟩
  intro a ha
  rw [show a = algebraMap R A (g a) + (a - algebraMap R A (g a)) by ring]
  exact Submodule.add_mem_sup (mem_map_of_mem _ (map_nonunit (g : A →+* R) a ha))
    (by simp [RingHom.mem_ker])

end IsLocalRing

section Regular

variable [IsRegularLocalRing R] [IsRegularLocalRing A]

/-- The closed fibre has embedding dimension at most `dim A - dim R`. -/
private theorem spanFinrank_map_add_spanFinrank_le (g : A →ₐ[R] R) :
    ((maximalIdeal A).map (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R A)))).spanFinrank
      + (maximalIdeal R).spanFinrank ≤ (maximalIdeal A).spanFinrank := by
  set I := (maximalIdeal R).map (algebraMap R A)
  have hsurj : Function.Surjective g := fun r ↦ ⟨algebraMap R A r, by simp⟩
  have : IsRegularLocalRing (A ⧸ RingHom.ker g) :=
    .of_ringEquiv (RingHom.quotientKerEquivOfSurjective hsurj).symm
  -- the kernel of `g` is cut out by the first `count` entries of a regular system of parameters
  obtain ⟨size, count, gens, hcount, hspan, hsize, hker⟩ :=
    exists_regularSystem_of_quotient (RingHom.ker g)
  have hkerle : RingHom.ker g ≤ maximalIdeal A := le_maximalIdeal (RingHom.ker_ne_top g)
  -- modulo `I`, the maximal ideal of `A` is generated by those `count` parameters
  have hfibre : (maximalIdeal A).map (Ideal.Quotient.mk I) =
      span (Set.range fun i : Fin count ↦ Ideal.Quotient.mk I (gens (Fin.castLE hcount i))) := by
    refine le_antisymm ?_ (le_trans ?_ (map_mono hkerle))
    · refine (map_mono (maximalIdeal_le_map_sup_ker g)).trans ?_
      rw [Ideal.map_sup, map_quotient_self, bot_sup_eq, hker, map_span]
      refine span_mono ?_
      rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rw [hker, map_span]
      refine span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact subset_span ⟨_, ⟨_, i.isLt, rfl⟩, rfl⟩
  have h₁ : ((maximalIdeal A).map (Ideal.Quotient.mk I)).spanFinrank ≤ count :=
    (Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family
      (Ideal.fg_of_isNoetherianRing _) _).mpr ⟨_, hfibre.symm⟩
  -- `g` kills those parameters and carries the remaining ones onto generators of `𝔪_R`
  have hR : span (Set.range fun i : Fin (size - count) ↦ g (gens ⟨count + i, by omega⟩)) =
      maximalIdeal R := by
    rw [← map_maximalIdeal_of_surjective (g : A →+* R) hsurj, ← hspan, map_span]
    refine le_antisymm (span_mono ?_) (span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      by_cases hi : (i : ℕ) < count
      · have : gens i ∈ RingHom.ker g := hker ▸ subset_span ⟨i, hi, rfl⟩
        have h0 : g (gens i) = 0 := RingHom.mem_ker.mp this
        simp [h0]
      · exact subset_span ⟨⟨i - count, by omega⟩, congrArg (g ∘ gens) (Fin.ext (by simp; omega))⟩
  have h₂ : (maximalIdeal R).spanFinrank ≤ size - count :=
    (Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family
      (maximalIdeal R).fg_of_isNoetherianRing _).mpr ⟨_, hR⟩
  omega

/-- The closed fibre is regular and dimension adds up: its embedding dimension is at most
`dim A - dim R`, which Krull's height theorem bounds by its dimension. -/
private theorem isRegularLocalRing_quotient_and_ringKrullDim_eq (g : A →ₐ[R] R) :
    IsRegularLocalRing (A ⧸ (maximalIdeal R).map (algebraMap R A)) ∧
      ringKrullDim A = ringKrullDim R + ringKrullDim (A ⧸ (maximalIdeal R).map (algebraMap R A))
      := by
  have := g.isLocalHom_algebraMap
  have hI : (maximalIdeal R).map (algebraMap R A) ≤ maximalIdeal A :=
    map_le_iff_le_comap.mpr fun r hr ↦ map_nonunit _ r hr
  -- `I` is generated by the images of `dim R` generators of `𝔪_R`
  have h₂ : ((maximalIdeal R).map (algebraMap R A)).spanFinrank ≤
      (maximalIdeal R).spanFinrank := by
    obtain ⟨f, hf⟩ := (Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family
      (maximalIdeal R).fg_of_isNoetherianRing _).mp le_rfl
    refine (Submodule.FG.spanFinrank_le_iff_exists_fin_generating_family
      (fg_of_isNoetherianRing _) _).mpr ⟨algebraMap R A ∘ f, ?_⟩
    rw [Set.range_comp, Ideal.submodule_span_eq, ← map_span, ← Ideal.submodule_span_eq, hf]
  have h₁ := g.spanFinrank_map_add_spanFinrank_le
  generalize (maximalIdeal R).map (algebraMap R A) = I at hI h₁ h₂ ⊢
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
    (maximalIdeal.isMaximal A).ne_top hI)
  have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hdim := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
    (IsLocalRing.ringJacobson_eq_maximalIdeal A ▸ hI)
  have hle := ringKrullDim_le_spanFinrank_maximalIdeal (A ⧸ I)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h₁
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)] at hdim
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A),
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)]
  -- the dimension of the closed fibre is a natural number, at most its embedding dimension
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim (A ⧸ I) = n := by
    obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := A ⧸ I))
    obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp
      (show m ≠ ⊤ by rintro rfl; rw [← hm] at hle; exact absurd hle (by norm_cast))
    exact ⟨n, hm.symm⟩
  rw [hn] at hle hdim ⊢
  norm_cast at hle hdim ⊢
  exact ⟨.of_spanFinrank_maximalIdeal_le _ (by rw [hn]; exact_mod_cast (by omega)), by omega⟩

/-- **The closed fibre of a regular local algebra with a retraction is regular.** If `R` and `A`
are regular local rings and `A` has an `R`-algebra retraction `A →ₐ[R] R`, then
`A ⧸ 𝔪_R A` is a regular local ring. -/
theorem isRegularLocalRing_quotient_map_maximalIdeal (g : A →ₐ[R] R) :
    IsRegularLocalRing (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
  g.isRegularLocalRing_quotient_and_ringKrullDim_eq.1

/-- **Dimension is additive along a retraction.** If `R` and `A` are regular local rings and `A`
has an `R`-algebra retraction, then `dim A = dim R + dim (A ⧸ 𝔪_R A)`. -/
theorem ringKrullDim_eq_add_ringKrullDim_quotient (g : A →ₐ[R] R) :
    ringKrullDim A = ringKrullDim R + ringKrullDim (A ⧸ (maximalIdeal R).map (algebraMap R A)) :=
  g.isRegularLocalRing_quotient_and_ringKrullDim_eq.2

/-- **A regular local algebra with a retraction to a regular local base is flat.** This is miracle
flatness, as `A` is Cohen–Macaulay and its dimension is that of `R` plus that of its closed fibre.
-/
theorem flat_of_isRegularLocalRing (g : A →ₐ[R] R) : Module.Flat R A :=
  have := g.isLocalHom_algebraMap
  TauCeti.Algebra.flat_of_isCohenMacaulay TauCeti.IsRegularLocalRing.isCohenMacaulay
    g.ringKrullDim_eq_add_ringKrullDim_quotient

/-- **A regular local algebra with a retraction to a regular local base is formally smooth**, when
it is essentially of finite presentation: a localization of a finitely presented `R`-algebra `P`.
-/
theorem formallySmooth_of_isRegularLocalRing (g : A →ₐ[R] R) {P : Type*} [CommRing P]
    [Algebra R P] [Algebra P A] [IsScalarTower R P A] (M : Submonoid P) [IsLocalization M A]
    [Algebra.FinitePresentation R P] :
    Algebra.FormallySmooth R A := by
  have := g.isLocalHom_algebraMap
  have := g.flat_of_isRegularLocalRing
  have := g.isRegularLocalRing_quotient_map_maximalIdeal
  let k := ResidueField R
  let e : k ⊗[R] A ≃+* A ⧸ (maximalIdeal R).map (algebraMap R A) :=
    (Algebra.TensorProduct.comm R k A).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal R)).symm.toRingEquiv
  have : IsRegularLocalRing (k ⊗[R] A) := .of_ringEquiv e.symm
  have : Algebra.EssFiniteType R A :=
    have : Algebra.EssFiniteType P A := .of_isLocalization A M
    .comp R P A
  -- the residue field of the closed fibre is `k`
  have hsurj : Function.Surjective (algebraMap k (ResidueField (k ⊗[R] A))) := by
    let ι : A →+* k ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
    have hinc : Function.Surjective ι := TensorProduct.mk_surjective _ _ _ residue_surjective
    intro x
    obtain ⟨y, rfl⟩ := residue_surjective x
    obtain ⟨a, rfl⟩ := hinc y
    refine ⟨residue R (g a), ?_⟩
    have hmem : a - algebraMap R A (g a) ∈ maximalIdeal A :=
      le_maximalIdeal (RingHom.ker_ne_top g) (by simp [RingHom.mem_ker])
    have := mem_map_of_mem ι hmem
    rw [map_maximalIdeal_of_surjective _ hinc, ← residue_eq_zero_iff, map_sub, map_sub,
      sub_eq_zero] at this
    rw [this, IsScalarTower.algebraMap_apply k (k ⊗[R] A) (ResidueField (k ⊗[R] A)),
      ResidueField.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply]
    simp [ι, k]
  have : Algebra.FormallySmooth k (ResidueField (k ⊗[R] A)) :=
    .of_equiv (AlgEquiv.ofBijective (Algebra.ofId k _) ⟨(algebraMap k _).injective, hsurj⟩)
  have : Algebra.FormallySmooth k (k ⊗[R] A) := TauCeti.formallySmooth_of_isRegularLocalRing
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor M

end Regular

end AlgHom

/-- **Smoothness at a point through which a section passes.** Let `S` be a finitely presented
`R`-algebra and `q` a prime of `S` over the prime `p` of `R`, with both local rings `R_p` and `S_q`
regular. If the map `R_p → S_q` has a left inverse ring homomorphism, then `S` is smooth over `R`
at `q`.

The reduction to the local statement follows that of Mathlib's
`Algebra.IsSmoothAt.of_formallySmooth_fiber`. -/
theorem Algebra.IsSmoothAt.of_isRegularLocalRing {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (p : Ideal R) (q : Ideal S) [p.IsPrime]
    [q.IsPrime] [q.LiesOver p] [IsRegularLocalRing (Localization.AtPrime p)]
    [IsRegularLocalRing (Localization.AtPrime q)]
    (g : Localization.AtPrime q →+* Localization.AtPrime p)
    (hg : g.comp (Localization.localRingHom p q (algebraMap R S) Ideal.LiesOver.over) =
      RingHom.id _) :
    Algebra.IsSmoothAt R q := by
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  -- `S_q` is a localization of `S_p`, which is finitely presented over `R_p`
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid S p.primeCompl)
      (f := Algebra.ofId _ _) (by
    rintro ⟨_, x, hx, rfl⟩
    simpa using! IsLocalization.map_units (M := q.primeCompl) Sq ⟨algebraMap _ _ x,
      by simp_all [q.over_def p]⟩)
  algebraize [f.toRingHom]
  have : IsScalarTower R Sp Sq := .to₁₃₄ _ S _ _
  have : IsScalarTower Rp Sp Sq := .of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext p.primeCompl
    simp only [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    .isLocalization_of_submonoid_le _ _ (Algebra.algebraMapSubmonoid S p.primeCompl) _
    (by rintro _ ⟨x, hx, rfl⟩; simp_all [q.over_def p])
  have : Algebra.FinitePresentation Rp Sp := by
    have : Algebra.IsPushout R Rp S Sp :=
      .symm <| Algebra.isPushout_of_isLocalization p.primeCompl _ _ _
    exact .equiv (Algebra.IsPushout.equiv R Rp S Sp)
  let g' : Sq →ₐ[Rp] Rp := { g with commutes' := fun r ↦ congr($hg r) }
  have := g'.formallySmooth_of_isRegularLocalRing (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  exact .comp R Rp Sq
