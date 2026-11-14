/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Filtration
public import TauCeti.Algebra.Module.Submodule.Essential
public import TauCeti.RingTheory.AdicCompletion.Algebra
public import TauCeti.RingTheory.AdicCompletion.Noetherian
public import TauCeti.RingTheory.AdicCompletion.Torsion

/-!
# Injectivity and submodule lattice of ideal-power-torsion modules over the completion

Let `I` be an ideal of a commutative ring `R`, let `R̂ = AdicCompletion I R`, and let `M` be an
`R`-module in which every element is killed by a power of `I`. By
`TauCeti.AdicCompletion.torsionModule`, `M` carries a canonical `R̂`-module structure in which each
completed scalar acts on an `I ^ n`-torsion element through its residue modulo `I ^ n`.

More generally, when `I` is finitely generated, any `R`-linear map out of an
`I`-power-torsion `R̂`-module whose `R̂`-action extends `R` is automatically `R̂`-linear for
any compatible `R̂`-action on the codomain
(`TauCeti.AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent`), avoiding typeclass
diamonds when Hom modules already carry a completion action. Because every `R̂`-scalar acts
on a given element of `M` as some scalar from `R`, the `R̂`-submodules and `R`-submodules
of `M` coincide (`TauCeti.AdicCompletion.torsionSubmoduleOrderIso`). Hence Artinianness,
Noetherianity, and essentiality of submodules of `M` are unchanged when passing between
`R` and `R̂`.

When `R` is Noetherian, `R̂` is Noetherian (`Ideal.isNoetherianRing_adicCompletion`). Using Baer's
criterion and the Artin–Rees lemma on ideals of `R̂`, any `I`-power-torsion `R`-module satisfying
Baer's criterion over `R` also satisfies Baer's criterion over `R̂`, so injectivity of `M` over `R`
lifts to injectivity over `R̂` (`TauCeti.AdicCompletion.torsionModule_injective`, Stacks Project
Tag 08Z5). Moreover, `[Small.{v} R]` supplies `[Small.{v} R̂]` via
`TauCeti.AdicCompletion.instSmall`. Combining `TauCeti.AdicCompletion.torsionLiftEquiv` with
`TauCeti.AdicCompletion.ofTensorProductEquiv` also gives the tensor-Hom comparison
`(N →ₗ[R] M) ≃ₗ[R̂] (R̂ ⊗[R] N →ₗ[R̂] M)` for finitely generated `R`-modules `N`.

## Main declarations

* `TauCeti.AdicCompletion.instSmall`: `AdicCompletion I M` is `Small.{v}` whenever `M` is
  `Small.{v}`.
* `LinearMap.map_adicCompletion_smul_of_mem_primaryComponent` and
  `TauCeti.AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent`: for finitely generated `I`,
  `R`-linear maps out of an `I`-power-torsion `R̂`-module coincide with `R̂`-linear maps for any
  compatible `R̂`-actions.
* `TauCeti.AdicCompletion.torsionSubmoduleOrderIso`: restriction of scalars is an order isomorphism
  `Submodule (AdicCompletion I R) M ≃o Submodule R M` on an `I`-power-torsion module.
* `TauCeti.AdicCompletion.torsionModule_baer` and `TauCeti.AdicCompletion.torsionModule_injective`:
  Baer's criterion and module injectivity lift from `R` to `AdicCompletion I R` over a Noetherian
  ring `R`.
* `TauCeti.AdicCompletion.torsionTensorLiftEquiv`: the `R̂`-linear equivalence
  `(N →ₗ[R] M) ≃ₗ[R̂] (AdicCompletion I R ⊗[R] N →ₗ[AdicCompletion I R] M)` for finite `N` over
  Noetherian `R`.

## References

* [Stacks Project, Lemma 47.7.4](https://stacks.math.columbia.edu/tag/08Z5)
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

universe u v w

namespace TauCeti.AdicCompletion

/-- The adic completion of a `Small.{v}` module is `Small.{v}`, as a subtype of a countable
product of quotients of `M`. In particular `[Small.{v} R]` supplies
`[Small.{v} (AdicCompletion I R)]` for module injectivity over the completion. -/
instance instSmall {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M]
    [Module R M] [Small.{v} M] : Small.{v} (_root_.AdicCompletion I M) := by
  have (n : ℕ) : Small.{v} (M ⧸ (I ^ n • ⊤ : Submodule R M)) :=
    small_of_surjective (Submodule.Quotient.mk_surjective _)
  exact small_of_injective (f := Subtype.val) Subtype.val_injective

/-- On any `AdicCompletion I R`-module compatible with `R`, a completed scalar congruent to `r : R`
modulo `I ^ n R̂` acts as `r` on every `I ^ n`-torsion element. -/
theorem smul_eq_of_sub_algebraMap_mem_map_pow {R : Type*} [CommRing R] {I : Ideal R}
    {P : Type*} [AddCommGroup P] [Module R P] [Module (_root_.AdicCompletion I R) P]
    [IsScalarTower R (_root_.AdicCompletion I R) P] {x : P} {n : ℕ}
    (hx : x ∈ Submodule.torsionBySet R P ↑(I ^ n)) {a : _root_.AdicCompletion I R} {r : R}
    (ha : a - algebraMap R (_root_.AdicCompletion I R) r ∈
      (I ^ n).map (algebraMap R (_root_.AdicCompletion I R))) :
    a • x = r • x := by
  have hle : (I ^ n).map (algebraMap R (_root_.AdicCompletion I R)) ≤
      LinearMap.ker (LinearMap.toSpanSingleton (_root_.AdicCompletion I R) P x) := by
    rw [Ideal.map_le_iff_le_comap]
    intro m hm
    simpa [LinearMap.mem_ker, algebraMap_smul] using
      (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨m, hm⟩
  have hzero : (a - algebraMap R (_root_.AdicCompletion I R) r) • x = 0 := hle ha
  rwa [sub_smul, algebraMap_smul, sub_eq_zero] at hzero

end TauCeti.AdicCompletion

namespace LinearMap

/-- When `I` is finitely generated, every `R`-linear map out of an `I`-power-torsion
`AdicCompletion I R`-module is automatically `AdicCompletion I R`-linear for any compatible
`AdicCompletion I R`-module structure on the codomain. -/
theorem map_adicCompletion_smul_of_mem_primaryComponent {R : Type*} [CommRing R] {I : Ideal R}
    {P Q : Type*} [AddCommGroup P] [Module R P] [Module (AdicCompletion I R) P]
    [IsScalarTower R (AdicCompletion I R) P]
    [AddCommGroup Q] [Module R Q] [Module (AdicCompletion I R) Q]
    [IsScalarTower R (AdicCompletion I R) Q]
    (f : P →ₗ[R] Q) (fg : I.FG) (hP : ∀ x : P, x ∈ I.primaryComponent P)
    (a : AdicCompletion I R) (x : P) :
    f (a • x) = a • f x := by
  obtain ⟨n, hn⟩ := (I.primaryComponent_mem P x).mp (hP x)
  have hfn : f x ∈ Submodule.torsionBySet R Q ↑(I ^ n) := by
    rw [Submodule.mem_torsionBySet_iff] at hn ⊢
    intro m
    rw [← f.map_smul, hn m, f.map_zero]
  obtain ⟨r, hr⟩ := AdicCompletion.exists_sub_algebraMap_mem_map_pow fg n a
  rw [TauCeti.AdicCompletion.smul_eq_of_sub_algebraMap_mem_map_pow hn hr,
    TauCeti.AdicCompletion.smul_eq_of_sub_algebraMap_mem_map_pow hfn hr, f.map_smul]

end LinearMap

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion TensorProduct

section CompatibleAction

variable {R : Type u} [CommRing R] {I : Ideal R}
  {P : Type w} [AddCommGroup P] [Module R P] [Module (_root_.AdicCompletion I R) P]
  [IsScalarTower R (_root_.AdicCompletion I R) P]
  {Q : Type v} [AddCommGroup Q] [Module R Q] [Module (_root_.AdicCompletion I R) Q]
  [IsScalarTower R (_root_.AdicCompletion I R) Q]

/-- Restriction of scalars identifies `AdicCompletion I R`-linear maps out of an `I`-power-torsion
`AdicCompletion I R`-module with `R`-linear maps, using the given module structures without creating
typeclass diamonds. -/
def restrictScalarsEquivOfMemPrimaryComponent (fg : I.FG)
    (hP : ∀ x : P, x ∈ I.primaryComponent P) :
    (P →ₗ[_root_.AdicCompletion I R] Q) ≃ₗ[_root_.AdicCompletion I R] (P →ₗ[R] Q) where
  __ := LinearMap.restrictScalarsₗ R (_root_.AdicCompletion I R) P Q (_root_.AdicCompletion I R)
  invFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_adicCompletion_smul_of_mem_primaryComponent fg hP }
  left_inv _ := LinearMap.ext fun _ ↦ rfl
  right_inv _ := LinearMap.ext fun _ ↦ rfl

@[simp]
theorem restrictScalarsEquivOfMemPrimaryComponent_apply (fg : I.FG)
    (hP : ∀ x : P, x ∈ I.primaryComponent P)
    (f : P →ₗ[_root_.AdicCompletion I R] Q) (x : P) :
    restrictScalarsEquivOfMemPrimaryComponent fg hP f x = f x :=
  (rfl)

@[simp]
theorem restrictScalarsEquivOfMemPrimaryComponent_symm_apply (fg : I.FG)
    (hP : ∀ x : P, x ∈ I.primaryComponent P) (f : P →ₗ[R] Q) (x : P) :
    (restrictScalarsEquivOfMemPrimaryComponent fg hP).symm f x = f x :=
  (rfl)

end CompatibleAction

section SubmoduleLattice

variable {R : Type u} [CommRing R] {I : Ideal R}
  {M : Type w} [AddCommGroup M] [Module R M]
  (hM : ∀ x : M, x ∈ I.primaryComponent M)

/-- On an `I`-power-torsion module, restriction of scalars from `AdicCompletion I R` to `R` is an
order isomorphism of submodule lattices: every `R`-submodule is stable under the completion action
because completed scalars act pointwise through residues in `R`. -/
def torsionSubmoduleOrderIso :
    letI := torsionModule hM
    Submodule (_root_.AdicCompletion I R) M ≃o Submodule R M := by
  let := torsionModule hM
  have := torsionModule_isScalarTower hM
  exact
    { toFun := Submodule.restrictScalars R
      invFun N :=
        { N with
          smul_mem' a x hx := by
            obtain ⟨n, hn⟩ := (I.primaryComponent_mem M x).mp (hM x)
            obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n a)
            rw [a.torsion_smul_eq hM x r hn hr.symm]
            exact N.smul_mem r hx }
      left_inv P := Submodule.ext fun _ ↦ Iff.rfl
      right_inv N := Submodule.ext fun _ ↦ Iff.rfl
      map_rel_iff' := Iff.rfl }

@[simp]
theorem torsionSubmoduleOrderIso_apply
    (P : letI := torsionModule hM; Submodule (_root_.AdicCompletion I R) M) :
    torsionSubmoduleOrderIso hM P =
      (letI := torsionModule hM
       haveI := torsionModule_isScalarTower hM
       P.restrictScalars R) :=
  (rfl)

@[simp]
theorem mem_torsionSubmoduleOrderIso_symm (N : Submodule R M) (x : M) :
    x ∈ (torsionSubmoduleOrderIso hM).symm N ↔ x ∈ N :=
  Iff.rfl

/-- An `I`-power-torsion module is Artinian over `AdicCompletion I R` if and only if it is Artinian
over `R`. -/
theorem isArtinian_torsionModule_iff :
    letI := torsionModule hM
    IsArtinian (_root_.AdicCompletion I R) M ↔ IsArtinian R M := by
  let := torsionModule hM
  have := torsionModule_isScalarTower hM
  exact ⟨fun h ↦ (torsionSubmoduleOrderIso hM).symm.toOrderEmbedding.wellFounded h,
    isArtinian_of_tower R⟩

/-- An `I`-power-torsion module is Noetherian over `AdicCompletion I R` if and only if it is
Noetherian over `R`. -/
theorem isNoetherian_torsionModule_iff :
    letI := torsionModule hM
    IsNoetherian (_root_.AdicCompletion I R) M ↔ IsNoetherian R M := by
  let := torsionModule hM
  rw [isNoetherian_iff, isNoetherian_iff]
  exact ⟨fun h ↦ (torsionSubmoduleOrderIso hM).symm.dual.toOrderEmbedding.wellFounded h,
    fun h ↦ (torsionSubmoduleOrderIso hM).dual.toOrderEmbedding.wellFounded h⟩

/-- Essentiality of a submodule of an `I`-power-torsion module agrees over `AdicCompletion I R` and
over `R`. -/
theorem isEssential_restrictScalars_torsionModule_iff
    (P : letI := torsionModule hM; Submodule (_root_.AdicCompletion I R) M) :
    (letI := torsionModule hM
     haveI := torsionModule_isScalarTower hM
     IsEssential (P.restrictScalars R)) ↔
    (letI := torsionModule hM; IsEssential P) := by
  let e := torsionSubmoduleOrderIso hM
  rw [← torsionSubmoduleOrderIso_apply hM P]
  let := torsionModule hM
  rw [isEssential_iff, isEssential_iff]
  constructor
  · intro h Q hQ
    apply e.injective
    rw [map_bot]
    exact h (e Q) (by rw [← map_inf, hQ, map_bot])
  · intro h N hN
    apply e.symm.injective
    rw [map_bot]
    refine h (e.symm N) ?_
    apply e.injective
    rw [map_inf, e.apply_symm_apply, hN, map_bot]

/-- When `I` is finitely generated, every element of an `I`-power-torsion module lies in the
primary component of the extended ideal `I R̂` in `AdicCompletion I R`. -/
theorem mem_map_primaryComponent_torsionModule (fg : I.FG) (x : M) :
    letI := torsionModule hM
    x ∈ (I.map (algebraMap R (_root_.AdicCompletion I R))).primaryComponent M := by
  let := torsionModule hM
  obtain ⟨n, hn⟩ := (I.primaryComponent_mem M x).mp (hM x)
  refine ((I.map (algebraMap R (_root_.AdicCompletion I R))).primaryComponent_mem M x).mpr ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  rintro ⟨a, ha⟩
  rw [SetLike.mem_coe, ← Ideal.map_pow, ← ker_evalₐ_eq_map_pow fg n, RingHom.mem_ker] at ha
  have hzero : evalₐ I n a = Ideal.Quotient.mk (I ^ n) 0 := by simpa using ha
  rw [a.torsion_smul_eq hM x 0 hn hzero, zero_smul]

end SubmoduleLattice

section Noetherian

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
  {M : Type w} [AddCommGroup M] [Module R M]
  (hM : ∀ x : M, x ∈ I.primaryComponent M)

/-- By Artin–Rees on ideals of the Noetherian completion `R̂`, any `R̂`-linear map out of an ideal
`𝔟` of `R̂` into an `I`-power-torsion module vanishes on `𝔟 ⊓ I ^ m R̂` for some `m : ℕ`. -/
private theorem exists_ker_evalₐ_le_ker_of_torsionModule
    (𝔟 : Ideal (_root_.AdicCompletion I R))
    (g : letI := torsionModule hM; 𝔟 →ₗ[_root_.AdicCompletion I R] M) :
    letI := torsionModule hM
    haveI := torsionModule_isScalarTower hM
    ∃ m : ℕ, LinearMap.ker ((evalₐ I m).toLinearMap ∘ₗ 𝔟.subtype.restrictScalars R) ≤
      LinearMap.ker (g.restrictScalars R) := by
  let A := _root_.AdicCompletion I R
  let := torsionModule hM
  have := torsionModule_isScalarTower hM
  let IA : Ideal A := I.map (algebraMap R A)
  have hfg : I.FG := IsNoetherian.noetherian I
  obtain ⟨n, hn⟩ := IA.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent g
    fun b ↦ mem_map_primaryComponent_torsionModule hM hfg (g b)
  obtain ⟨k, hk⟩ := IA.exists_pow_inf_eq_pow_smul (M := A) 𝔟
  refine ⟨n + k, fun b hb ↦ ?_⟩
  have hm : IA ^ (n + k) ⊓ 𝔟 ≤ IA ^ n • 𝔟 := by
    have hmk := hk (n + k) (Nat.le_add_left k n)
    simp only [smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_right] at hmk
    exact hmk.le.trans (Submodule.smul_mono le_rfl inf_le_right)
  have hbm : (b : A) ∈ IA ^ (n + k) := by
    rw [← Ideal.map_pow, ← ker_evalₐ_eq_map_pow hfg (n + k)]
    exact hb
  have hmem : (b : A) ∈ (LinearMap.ker g).map 𝔟.subtype := by
    refine Submodule.smul_le.mpr ?_ (hm ⟨hbm, b.2⟩)
    intro a ha c hc
    have hac : (⟨a * c, 𝔟.mul_mem_left a hc⟩ : 𝔟) = a • ⟨c, hc⟩ := Subtype.ext rfl
    refine ⟨⟨a * c, 𝔟.mul_mem_left a hc⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hac, map_smul]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hn ⟨c, hc⟩) ⟨a, ha⟩
  rcases hmem with ⟨⟨w, hw⟩, hgw, hw_eq⟩
  have hbw : b = ⟨w, hw⟩ := Subtype.ext hw_eq.symm
  exact hbw ▸ hgw

/-- Over a Noetherian ring `R`, an `I`-power-torsion `R`-module satisfying Baer's criterion over `R`
also satisfies Baer's criterion over `AdicCompletion I R`. -/
@[stacks 08Z5]
theorem torsionModule_baer (hBaer : Module.Baer R M) :
    letI := torsionModule hM
    Module.Baer (_root_.AdicCompletion I R) M := by
  let A := _root_.AdicCompletion I R
  let := torsionModule hM
  have := torsionModule_isScalarTower hM
  intro 𝔟 g
  obtain ⟨m, hker⟩ := exists_ker_evalₐ_le_ker_of_torsionModule hM 𝔟 g
  -- Factor `g` through the image of `𝔟` in `R ⧸ I ^ m`, then pull back to an ideal `K` of `R`.
  let p : 𝔟 →ₗ[R] R ⧸ I ^ m := (evalₐ I m).toLinearMap ∘ₗ 𝔟.subtype.restrictScalars R
  let gbar : LinearMap.range p →ₗ[R] M :=
    (LinearMap.ker p).liftQ (g.restrictScalars R) hker ∘ₗ p.quotKerEquivRange.symm.toLinearMap
  let K : Ideal R := (LinearMap.range p).comap (I ^ m).mkQ
  let q : K →ₗ[R] LinearMap.range p := ((I ^ m).mkQ ∘ₗ K.subtype).codRestrict _ fun x ↦ x.2
  obtain ⟨ψ, hψ⟩ := hBaer K (gbar ∘ₗ q)
  have hy₀ : ψ 1 ∈ Submodule.torsionBySet R M ↑(I ^ m) := by
    rw [Submodule.mem_torsionBySet_iff]
    rintro ⟨r, hr⟩
    have hr0 : (I ^ m).mkQ r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr
    have hrK : r ∈ K := Submodule.mem_comap.mpr (hr0 ▸ zero_mem p.range)
    have hqr : q ⟨r, hrK⟩ = 0 := Subtype.ext hr0
    rw [← map_smul, smul_eq_mul, mul_one, hψ r hrK, LinearMap.comp_apply, hqr, gbar.map_zero]
  refine ⟨LinearMap.toSpanSingleton A M (ψ 1), fun b hb ↦ ?_⟩
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I m b)
  have hrK : r ∈ K := Submodule.mem_comap.mpr (hr.symm ▸ LinearMap.mem_range_self p ⟨b, hb⟩)
  have hqb : q ⟨r, hrK⟩ = ⟨p ⟨b, hb⟩, LinearMap.mem_range_self p ⟨b, hb⟩⟩ := Subtype.ext hr
  rw [LinearMap.toSpanSingleton_apply, b.torsion_smul_eq hM (ψ 1) r hy₀ hr.symm, ← map_smul,
    smul_eq_mul, mul_one, hψ r hrK, LinearMap.comp_apply, hqb]
  simp [gbar]

/-- Over a Noetherian ring `R`, an injective `R`-module whose elements are each killed by a power
of `I` is injective over `AdicCompletion I R`. -/
@[stacks 08Z5]
theorem torsionModule_injective [Small.{w} R] [Module.Injective R M] :
    letI := torsionModule hM
    Module.Injective (_root_.AdicCompletion I R) M := by
  let := torsionModule hM
  exact (torsionModule_baer hM (Module.Baer.of_injective ‹_›)).injective

section TensorLift

variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- For a finitely generated module `N` over a Noetherian ring `R` and an `I`-power-torsion module
`M`, `R`-linear maps `N → M` correspond `R̂`-linearly to `R̂`-linear maps `R̂ ⊗[R] N → M`, combining
`torsionLiftEquiv` with `TauCeti.AdicCompletion.ofTensorProductEquiv`. -/
def torsionTensorLiftEquiv :
    letI := torsionModule hM
    (N →ₗ[R] M) ≃ₗ[_root_.AdicCompletion I R]
      (_root_.AdicCompletion I R ⊗[R] N →ₗ[_root_.AdicCompletion I R] M) := by
  let := torsionModule hM
  exact torsionLiftEquiv hM ≪≫ₗ
    LinearEquiv.congrLeft M (_root_.AdicCompletion I R) (ofTensorProductEquiv I N).symm

@[simp]
theorem torsionTensorLiftEquiv_apply_tmul (f : N →ₗ[R] M)
    (a : _root_.AdicCompletion I R) (x : N) :
    letI := torsionModule hM
    torsionTensorLiftEquiv hM f (a ⊗ₜ x) = a • f x := by
  let := torsionModule hM
  simp [torsionTensorLiftEquiv]

@[simp]
theorem torsionTensorLiftEquiv_symm_apply
    (g : letI := torsionModule hM
         _root_.AdicCompletion I R ⊗[R] N →ₗ[_root_.AdicCompletion I R] M) (x : N) :
    (torsionTensorLiftEquiv hM).symm g x = g (1 ⊗ₜ x) := by
  let := torsionModule hM
  simp [torsionTensorLiftEquiv]

end TensorLift

end Noetherian

end TauCeti.AdicCompletion
