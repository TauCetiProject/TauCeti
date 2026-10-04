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
import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.NormTrace

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
  refine hv (finprod_induction _ (one_mem _) (fun _ _ ↦ mul_mem) fun w ↦ ?_)
  refine HeightOneSpectrum.norm_mem_adicCompletionIntegers v w.1 ?_
  by_contra hw
  exact hvS ⟨w.1, hw, HeightOneSpectrum.ext w.2.over.symm⟩

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

end TauCeti.GlobalNumberFields
