/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Adeles.Extension
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Extension
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.IntegralClosure
public import TauCeti.RingTheory.Ideal.PrimesOver

import TauCeti.NumberTheory.NumberField.Global.Places.Semilocal
import TauCeti.NumberTheory.NumberField.InfinitePlace.Tower
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Norm.Trace
import TauCeti.RingTheory.DedekindDomain.PrimesAbove
import Mathlib.RingTheory.Norm.Transitivity

/-!
# The norm map of adeles

Let `L / K` be an extension of number fields. The norm of `L / K` extends to a multiplicative map
`N_{L/K} : 𝔸_L → 𝔸_K` of adele rings, defined place by place: the component of `N_{L/K}(x)` at a
place `v` of `K` is the product, over the finitely many places `w ∣ v` of `L`, of the local norms
`N_{L_w/K_v}(x_w)`. At an infinite place this includes the norm `z ↦ |z|²` of `ℂ` over `ℝ` when a
complex place lies over a real one.

The finite component is again a finite adele because the local norm carries the completed integer
ring `𝒪_w` into `𝒪_v` (`IsDedekindDomain.HeightOneSpectrum.norm_mem_adicCompletionIntegers`), and
only finitely many places of `K` lie below the finitely many places of `L` at which a given finite
adele of `L` is not integral.

The norm map is multiplicative but not additive. It extends the global norm along the diagonal
embeddings: placewise, this is the semilocal factorization `N_{L/K}(x) = ∏_{w ∣ v} N_{L_w/K_v}(x)`.
On adeles extended from `K` it is the `[L : K]`-th power, since the local degrees `[L_w : K_v]`
over a fixed place `v` add up to `[L : K]`. The induced maps on ideles and idele classes are in
`TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative`.

## Main definitions

* `TauCeti.GlobalNumberFields.finiteAdeleNorm`, `TauCeti.GlobalNumberFields.infiniteAdeleNorm`:
  the norm maps of finite and of infinite adeles.
* `TauCeti.GlobalNumberFields.adeleNorm`: the norm map `𝔸_L →* 𝔸_K` of adele rings.

## Main results

* `TauCeti.GlobalNumberFields.finiteAdeleNorm_apply`,
  `TauCeti.GlobalNumberFields.infiniteAdeleNorm_apply`: the component at a place `v` of `K` is the
  product of the local norms at the places above `v`.
* `TauCeti.GlobalNumberFields.adeleNorm_algebraMap`: the adele norm of a principal adele is the
  principal adele of the global norm.
* `TauCeti.GlobalNumberFields.adeleNorm_adeleExtension`: the adele norm of an adele extended from
  `K` is its `[L : K]`-th power.
* `TauCeti.GlobalNumberFields.adeleNorm_comp`: norm maps compose in towers of number fields.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, (8.4), and Chapter VI, §2.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-! ### Finite adeles -/

/-- The product of local norms above `v` is integral if every source coordinate above `v`
is integral. -/
theorem finprod_norm_mem_adicCompletionIntegers
    (x : ∀ w : HeightOneSpectrum (𝓞 L), w.adicCompletion L)
    (v : HeightOneSpectrum (𝓞 K))
    (hx : ∀ w, w.under (𝓞 K) = v → x w ∈ w.adicCompletionIntegers L) :
    (∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.norm (v.adicCompletion K) (x w.1)) ∈ v.adicCompletionIntegers K :=
  finprod_induction _ (one_mem _) (fun _ _ ↦ mul_mem) fun w ↦
    HeightOneSpectrum.norm_mem_adicCompletionIntegers v w.1
      (hx w.1 (HeightOneSpectrum.ext w.2.over.symm))

/-- The product over the places `w ∣ v` of the local norms of a finite adele of `L` lies in `𝒪_v`
for all but finitely many finite places `v` of `K`. -/
private theorem eventually_finprod_norm_mem_adicCompletionIntegers
    (x : FiniteAdeleRing (𝓞 L) L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K) (x w.1)) ∈ v.adicCompletionIntegers K := by
  have hx : {w : HeightOneSpectrum (𝓞 L) | x w ∉ w.adicCompletionIntegers L}.Finite :=
    Filter.eventually_cofinite.1 x.2
  -- Outside the places below the finitely many non-integral components, every factor is integral.
  refine Filter.eventually_cofinite.2 ((hx.image (HeightOneSpectrum.under (𝓞 K))).subset ?_)
  intro v hv
  by_contra hvS
  refine hv (finprod_norm_mem_adicCompletionIntegers K L x v fun w hwv ↦ ?_)
  by_contra hw
  exact hvS ⟨w, hw, hwv⟩

/-- **The norm map of finite adeles.** For an extension `L / K` of number fields, the component of
the norm of a finite adele `x` of `L` at a finite place `v` of `K` is `∏_{w ∣ v} N_{L_w/K_v}(x_w)`.
It is multiplicative but not additive. -/
def finiteAdeleNorm : FiniteAdeleRing (𝓞 L) L →* FiniteAdeleRing (𝓞 K) K where
  toFun x := ⟨fun v ↦ ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Algebra.norm (v.adicCompletion K) (x w.1),
    eventually_finprod_norm_mem_adicCompletionIntegers K L x⟩
  map_one' := FiniteAdeleRing.ext K fun _ ↦
    (congrArg finprod (funext fun _ ↦ map_one _)).trans finprod_one
  map_mul' _ _ := FiniteAdeleRing.ext K fun _ ↦
    (congrArg finprod (funext fun _ ↦ map_mul _ _ _)).trans
      (finprod_mul_distrib (Set.toFinite _) (Set.toFinite _))

variable {K L} in
/-- The component of the finite adele norm at `v` is the product of the local norms at the places
above `v`. -/
@[simp]
theorem finiteAdeleNorm_apply (x : FiniteAdeleRing (𝓞 L) L) (v : HeightOneSpectrum (𝓞 K)) :
    finiteAdeleNorm K L x v =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.norm (v.adicCompletion K) (x w.1) :=
  (rfl)

attribute [local instance] Fintype.ofFinite in
/-- The finite adele norm extends the norm of `L / K` along the diagonal embeddings. -/
@[simp]
theorem finiteAdeleNorm_algebraMap (x : L) :
    finiteAdeleNorm K L (algebraMap L (FiniteAdeleRing (𝓞 L) L) x) =
      algebraMap K (FiniteAdeleRing (𝓞 K) K) (Algebra.norm K x) := by
  refine FiniteAdeleRing.ext K fun v ↦ ?_
  rw [finiteAdeleNorm_apply, finprod_eq_prod_of_fintype]
  -- The diagonal components `algebraMap L _ x w` and `algebraMap K _ y v` are the images of `x`
  -- and `y` in the completions, as in the semilocal norm formula.
  exact (TauCeti.algebraMap_norm_eq_prod_norm L v x).symm

attribute [local instance] Fintype.ofFinite in
/-- The norm of a finite adele extended from `K` is its `[L : K]`-th power. -/
@[simp]
theorem finiteAdeleNorm_finiteAdeleExtension (a : FiniteAdeleRing (𝓞 K) K) :
    finiteAdeleNorm K L (finiteAdeleExtension (𝓞 K) K (𝓞 L) L a) = a ^ Module.finrank K L := by
  refine FiniteAdeleRing.ext K fun v ↦ ?_
  have h (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) :
      Algebra.norm (v.adicCompletion K) (finiteAdeleExtension (𝓞 K) K (𝓞 L) L a w.1) =
        a v ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
    obtain ⟨w, hw⟩ := w
    obtain rfl : w.under (𝓞 K) = v := HeightOneSpectrum.ext hw.over.symm
    rw [finiteAdeleExtension_apply, ← HeightOneSpectrum.algebraMap_adicCompletionExtensionAlgebra,
      Algebra.norm_algebraMap]
  rw [finiteAdeleNorm_apply, finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun w _ ↦ h w,
    Finset.prod_pow_eq_pow_sum, TauCeti.sum_finrank_adicCompletion_eq_finrank]
  exact (RestrictedProduct.pow_apply (x := a) (i := v) ..).symm

/-- Norm maps of finite adeles compose in a tower `K ⊆ L ⊆ M`. -/
@[simp]
theorem finiteAdeleNorm_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (finiteAdeleNorm K L).comp (finiteAdeleNorm L M) = finiteAdeleNorm K M := by
  apply MonoidHom.ext
  intro x
  apply FiniteAdeleRing.ext K
  intro v
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  let _ (w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}) :
      Fintype {u : HeightOneSpectrum (𝓞 M) // u.asIdeal.LiesOver w.1.asIdeal} :=
    Fintype.ofFinite _
  let _ : Fintype {u : HeightOneSpectrum (𝓞 M) // u.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  simp only [MonoidHom.comp_apply, finiteAdeleNorm_apply]
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]
  simp_rw [finprod_eq_prod_of_fintype, map_prod]
  rw [← Fintype.prod_sigma']
  let e := HeightOneSpectrum.liesOverTowerEquiv (R := 𝓞 L) (C := 𝓞 M) v
  refine Fintype.prod_equiv e _ _ fun p ↦ ?_
  let _ : p.2.1.asIdeal.LiesOver p.1.1.asIdeal := p.2.2
  let _ : p.1.1.asIdeal.LiesOver v.asIdeal := p.1.2
  let _ : p.2.1.asIdeal.LiesOver v.asIdeal :=
    Ideal.LiesOver.trans p.2.1.asIdeal p.1.1.asIdeal v.asIdeal
  -- The `K`-algebra structure on the completion at `(e p).1` depends on the proof `(e p).2`, so
  -- rewriting only the projection `(e p).1` fails (the motive is not type correct); rewrite the
  -- whole subtype element instead.
  rw [show e p = ⟨p.2.1, inferInstance⟩ from
    Subtype.ext (HeightOneSpectrum.liesOverTowerEquiv_apply (𝓞 L) v p)]
  refine @Algebra.norm_norm _ _ _ _ _ _ _ _ _ _ ?_ _ _
  exact IsScalarTower.of_algebraMap_eq fun y ↦ by
    rw [HeightOneSpectrum.algebraMap_eq_completionAlgHom (K := K) v p.2.1,
      HeightOneSpectrum.algebraMap_eq_completionAlgHom (K := L) p.1.1 p.2.1,
      HeightOneSpectrum.algebraMap_eq_completionAlgHom (K := K) v p.1.1]
    exact (AlgHom.congr_fun (HeightOneSpectrum.completionAlgHom_comp v p.1.1 p.2.1) y).symm

/-! ### Infinite adeles -/

/-- **The norm map of infinite adeles.** For an extension `L / K` of number fields, the component
of the norm of an infinite adele `x` of `L` at an infinite place `v` of `K` is
`∏_{w ∣ v} N_{L_w/K_v}(x_w)`. At a complex place above a real place the local norm is
`z ↦ |z|²`. -/
def infiniteAdeleNorm : InfiniteAdeleRing L →* InfiniteAdeleRing K where
  toFun x v := ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v}, Algebra.norm v.Completion (x w.1)
  map_one' := funext fun _ ↦ (congrArg finprod (funext fun _ ↦ map_one _)).trans finprod_one
  map_mul' _ _ := funext fun _ ↦ (congrArg finprod (funext fun _ ↦ map_mul _ _ _)).trans
    (finprod_mul_distrib (Set.toFinite _) (Set.toFinite _))

omit [NumberField K] in
variable {K L} in
/-- The component of the infinite adele norm at `v` is the product of the local norms at the
places above `v`. -/
@[simp]
theorem infiniteAdeleNorm_apply (x : InfiniteAdeleRing L) (v : InfinitePlace K) :
    infiniteAdeleNorm K L x v =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v}, Algebra.norm v.Completion (x w.1) :=
  (rfl)

/-- The infinite adele norm extends the norm of `L / K` along the diagonal embeddings. -/
@[simp]
theorem infiniteAdeleNorm_algebraMap (x : L) :
    infiniteAdeleNorm K L (algebraMap L (InfiniteAdeleRing L) x) =
      algebraMap K (InfiniteAdeleRing K) (Algebra.norm K x) := by
  classical
  funext v
  rw [infiniteAdeleNorm_apply, finprod_eq_prod_of_fintype]
  -- The diagonal components are the images of `x` and `N_{L/K}(x)` in the completions.
  exact (algebraMap_norm_eq_prod_norm_infiniteCompletion L v x).symm

/-- The norm of an infinite adele extended from `K` is its `[L : K]`-th power. -/
@[simp]
theorem infiniteAdeleNorm_infiniteAdeleExtension (a : InfiniteAdeleRing K) :
    infiniteAdeleNorm K L (infiniteAdeleExtension K L a) = a ^ Module.finrank K L := by
  classical
  funext v
  have h (w : {w : InfinitePlace L // w.LiesOver v}) :
      Algebra.norm v.Completion (infiniteAdeleExtension K L a w.1) =
        a v ^ Module.finrank v.Completion w.1.Completion := by
    obtain ⟨w, hw⟩ := w
    obtain rfl : w.comap (algebraMap K L) = v := InfinitePlace.LiesOver.comap_eq w v
    rw [infiniteAdeleExtension_apply]
    exact Algebra.norm_algebraMap _
  rw [infiniteAdeleNorm_apply, finprod_eq_prod_of_fintype, Finset.prod_congr rfl fun w _ ↦ h w,
    Finset.prod_pow_eq_pow_sum, sum_finrank_infiniteCompletion_eq_finrank]
  exact (Pi.pow_apply a _ v).symm

omit [NumberField K] in
/-- Norm maps of infinite adeles compose when `L` and `M` are number fields over a field `K`. -/
@[simp]
theorem infiniteAdeleNorm_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (infiniteAdeleNorm K L).comp (infiniteAdeleNorm L M) = infiniteAdeleNorm K M := by
  apply MonoidHom.ext
  intro x
  funext v
  let _ : Fintype {w : InfinitePlace L // w.LiesOver v} := Fintype.ofFinite _
  let _ (w : {w : InfinitePlace L // w.LiesOver v}) :
      Fintype {u : InfinitePlace M // u.LiesOver w.1} := Fintype.ofFinite _
  let _ : Fintype {u : InfinitePlace M // u.LiesOver v} := Fintype.ofFinite _
  simp only [MonoidHom.comp_apply, infiniteAdeleNorm_apply]
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype]
  simp_rw [finprod_eq_prod_of_fintype, map_prod]
  rw [← Fintype.prod_sigma']
  let e := InfinitePlace.liesOverTowerEquiv (L := L) (M := M) v
  refine Fintype.prod_equiv e _ _ fun p ↦ ?_
  let _ : p.2.1.LiesOver p.1.1 := p.2.2
  let _ : p.1.1.LiesOver v := p.1.2
  let _ : p.2.1.LiesOver v := LiesOver.trans p.2.1 p.1.1 v
  -- As in `finiteAdeleNorm_comp`, the completion algebra at `(e p).1` depends on `(e p).2`, so
  -- rewrite the whole subtype element rather than its projection.
  rw [show e p = ⟨p.2.1, inferInstance⟩ from
    Subtype.ext (InfinitePlace.liesOverTowerEquiv_apply v p)]
  refine @Algebra.norm_norm _ _ _ _ _ _ _ _ _ _ ?_ _ _
  exact IsScalarTower.of_algebraMap_eq fun y ↦
    (RingHom.congr_fun (LiesOver.completionMap_comp (v := v) (w := p.1.1)
      (u := p.2.1)) y).symm

/-! ### Adeles -/

/-- **The norm map of adeles** `N_{L/K} : 𝔸_L →* 𝔸_K`: `infiniteAdeleNorm` on the infinite
component and `finiteAdeleNorm` on the finite component. -/
def adeleNorm : AdeleRing (𝓞 L) L →* AdeleRing (𝓞 K) K :=
  (infiniteAdeleNorm K L).prodMap (finiteAdeleNorm K L)

variable {K L} in
/-- The infinite component of the adele norm is the infinite adele norm. -/
@[simp]
theorem adeleNorm_fst (x : AdeleRing (𝓞 L) L) :
    (adeleNorm K L x).1 = infiniteAdeleNorm K L x.1 :=
  (rfl)

variable {K L} in
/-- The finite component of the adele norm is the finite adele norm. -/
@[simp]
theorem adeleNorm_snd (x : AdeleRing (𝓞 L) L) :
    (adeleNorm K L x).2 = finiteAdeleNorm K L x.2 :=
  (rfl)

/-- The adele norm extends the norm of `L / K` along the diagonal embeddings: the norm of a
principal adele is the principal adele of the norm. -/
@[simp]
theorem adeleNorm_algebraMap (x : L) :
    adeleNorm K L (algebraMap L (AdeleRing (𝓞 L) L) x) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x) :=
  Prod.ext (by simp) (by simp)

/-- The norm of an adele extended from `K` is its `[L : K]`-th power. -/
@[simp]
theorem adeleNorm_adeleExtension (a : AdeleRing (𝓞 K) K) :
    adeleNorm K L (adeleExtension (𝓞 K) K (𝓞 L) L a) = a ^ Module.finrank K L :=
  -- Powers in `AdeleRing`, a type synonym for the product, are computed componentwise.
  Prod.ext
    (by rw [adeleNorm_fst, adeleExtension_fst, infiniteAdeleNorm_infiniteAdeleExtension]; rfl)
    (by rw [adeleNorm_snd, adeleExtension_snd, finiteAdeleNorm_finiteAdeleExtension]; rfl)

/-- Norm maps of adeles compose in a tower of number fields. -/
@[simp]
theorem adeleNorm_comp (M : Type*) [Field M] [NumberField M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] :
    (adeleNorm K L).comp (adeleNorm L M) = adeleNorm K M := by
  apply MonoidHom.ext
  intro x
  apply Prod.ext
  · simpa only [MonoidHom.comp_apply, adeleNorm_fst] using
      DFunLike.congr_fun (infiniteAdeleNorm_comp K L M) x.1
  · simpa only [MonoidHom.comp_apply, adeleNorm_snd] using
      DFunLike.congr_fun (finiteAdeleNorm_comp K L M) x.2

end TauCeti.GlobalNumberFields
