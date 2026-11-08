/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Tactic.Algebraize
import TauCeti.LinearAlgebra.TensorProduct.Submodule
import TauCeti.RingTheory.Flat.TensorProduct
import TauCeti.RingTheory.Ideal.TensorProduct
import TauCeti.RingTheory.TensorProduct.Finite

/-!
# The local criterion for flatness

Let `R` be a Noetherian ring, `S` a Noetherian `R`-algebra, `M` a finite `S`-module and `I` an
ideal of `R` whose extension `I S` lies in the Jacobson radical of `S`. If `I ⊗[R] M → M` is
injective, that is `Tor₁ᴿ(R ⧸ I, M) = 0`, and `M ⧸ I M` is flat over `R ⧸ I`, then `M` is flat
over `R` (`Module.Flat.of_subtype_rTensor_injective`). This is the local criterion for flatness
(Stacks, Tag 00MK), stated with the Jacobson radical in place of a local homomorphism of local
rings. For a local homomorphism `R → S` and `I` the maximal ideal of `R`, the quotient `M ⧸ I M`
is a vector space over the residue field, so flatness of `M` reduces to the vanishing of
`Tor₁ᴿ(κ, M)`. In its infinitesimal form the criterion needs no `Tor₁` hypothesis: `M` is flat
over `R` as soon as `M ⧸ Iⁿ M` is flat over `R ⧸ Iⁿ` for every `n`
(`Module.Flat.of_forall_flat_quotient_pow`), and conversely these quotients are flat when `M` is
(`Module.Flat.quotient_smul_top`). This form applies when `M` is only known modulo powers of `I`,
as for the completion of a ring that is flat over `R` but not yet known to be Noetherian.

Two special cases are derived.

* **A regular element** (Stacks, Tag 00ML, for the ideal `(x)`). If `x ∈ R` is `M`-regular, then
  `Tor₁ᴿ(R ⧸ (x), M) = 0` (`IsSMulRegular.span_singleton_subtype_rTensor_injective`), so `M` is
  flat over `R` as soon as `M ⧸ x M` is flat over `R ⧸ (x)` (`Module.Flat.of_flat_quotSMulTop`).
  Conversely `M ⧸ x M` is flat over `R ⧸ (x)` whenever `M` is flat over `R`, so for an
  `M`-regular `x` the two conditions are equivalent (`Module.flat_quotSMulTop_iff_flat`), the flat
  counterpart of Mathlib's `Module.free_quotSMulTop_iff_free`. This is the inductive step of
  miracle flatness (Stacks, Tag 00R4).
* **Flatness over the fibres** (Stacks, Tag 00MP). Let `R → S → T` be ring maps with `S` and `T`
  Noetherian, `M` a finite `T`-module flat over `R`, and `J` an ideal of `R` with `J T` in the
  Jacobson radical of `T`. Flatness over `R` already gives `Tor₁ˢ(S ⧸ J S, M) = 0`
  (`Module.Flat.map_subtype_rTensor_injective`, in `TauCeti.RingTheory.Ideal.TensorProduct`), so
  `M` is flat over `S` as soon as `M ⧸ J M` is flat over `S ⧸ J S`
  (`Module.Flat.of_flat_quotient_map`). For local rings and `J` the maximal ideal of `R`, the
  fibre condition holds automatically when `J S` is the maximal ideal of `S`; in ring
  homomorphism form, `f : S → T` is flat as soon as `f ∘ g` is, for some `g : R → S` with
  `𝔪_R S = 𝔪_S` (`RingHom.Flat.of_comp_of_map_maximalIdeal_eq`). The typical `g` is the map to
  the completion of a Noetherian local ring, which transports flatness of an endomorphism such as
  Frobenius to the completion.

Iterating the criterion along a sequence gives a flatness test for a local homomorphism `R → S`
of Noetherian local rings: if `r₁, …, rₙ` generate the maximal ideal of `R` and their images form
a weakly `S`-regular sequence, then `S` is flat over `R`
(`Module.Flat.of_isWeaklyRegular_map_algebraMap`). Dividing by `r₁` on both sides preserves the
hypotheses, and for `n = 0` the ring `R` is a field. The test needs no regularity of `R` or
Cohen–Macaulayness of `S`; these are only ways of producing the regular sequence. For instance,
the Frobenius endomorphism of a regular local ring of characteristic `p` sends a regular system
of parameters to their `p`-th powers, again a regular sequence, which proves Kunz's theorem
(`TauCeti.IsRegularLocalRing.flat_frobenius`). The ring homomorphism form
`RingHom.Flat.of_isWeaklyRegular_map` applies to such endomorphisms without an algebra
structure of a ring over itself.

## Implementation notes

By Mathlib's ideal criterion it suffices that `J ⊗[R] M → M` is injective for every ideal `J`.

Steps 1–3 hold without Noetherian hypotheses and live in `TauCeti.RingTheory.Flat.TensorProduct`.

1. Tensoring with `M` preserves injectivity of maps between modules killed by `I`: over `R ⧸ I`
   this is flatness of `M ⧸ I M` (`Ideal.rTensor_injective_of_isTorsionBySet`).
2. If `L ⧸ N` is killed by `I`, then `N ⊗[R] M → L ⊗[R] M` is injective, by a chase along a free
   module covering `L` (`Ideal.subtype_rTensor_injective_of_smul_top_le`).
3. By induction, the same holds when `L ⧸ N` is killed by `Iⁿ`
   (`Ideal.subtype_rTensor_injective_of_pow_smul_top_le`). Applied to `J ⧸ (J ⊓ Iⁿ)` inside
   `R ⧸ Iⁿ`, it shows that the kernel of `J ⊗[R] M → M` comes from `(J ⊓ Iⁿ) ⊗[R] M`
   (`Ideal.mem_range_rTensor_inclusion_inf_pow`).
4. By the Artin–Rees lemma `J ⊓ Iⁿ ⊆ I^(n - c) J`, so an element `t` of the kernel lies in
   `I^(n - c) (J ⊗[R] M)` for all `n`. Its image in `M ⊗[R] J`, a finite `S`-module
   (`Module.Finite.tensor`), therefore vanishes by Krull's intersection theorem over `S`.

For the infinitesimal form, step 3 is replaced by flatness of `M ⧸ Iⁿ M` over `R ⧸ Iⁿ`
(`Ideal.mem_range_rTensor_inclusion_inf_of_flat`), and step 4 is unchanged.

## Main results

* `Module.Flat.of_subtype_rTensor_injective`: the local criterion for flatness.
* `Module.Flat.of_forall_flat_quotient_pow`: the infinitesimal form of the local criterion;
  `Module.flat_iff_forall_flat_quotient_pow` is the equivalence.
* `Module.Flat.quotient_smul_top`: `M ⧸ I M` is flat over `R ⧸ I` when `M` is flat over `R`.
* `Module.Flat.of_flat_quotient_map`: the criterion for flatness over the fibres.
* `RingHom.Flat.of_comp_of_map_maximalIdeal_eq`: `f` is flat if `f ∘ g` is flat and `g` maps the
  maximal ideal onto the maximal ideal.
* `Module.Flat.of_flat_quotSMulTop`: the criterion along a regular element.
* `Module.Flat.quotSMulTop`: `M ⧸ x M` is flat over `R ⧸ (x)` when `M` is flat over `R`.
* `Module.flat_quotSMulTop_iff_flat`: for an `M`-regular `x` as above, `M ⧸ x M` is flat over
  `R ⧸ (x)` if and only if `M` is flat over `R`.
* `Module.Flat.of_isWeaklyRegular_map_algebraMap`: a local homomorphism `R → S` of Noetherian
  local rings is flat if generators of the maximal ideal of `R` map to a weakly `S`-regular
  sequence; `RingHom.Flat.of_isWeaklyRegular_map` is the same for a ring homomorphism.

## References

* [The Stacks Project, Tag 00MK](https://stacks.math.columbia.edu/tag/00MK), the local criterion
  for flatness, and Tag 00ML, its variant along a regular element.
* [The Stacks Project, Tag 00MP](https://stacks.math.columbia.edu/tag/00MP), flatness over the
  fibres.
* [The Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4), miracle flatness,
  whose proof uses the criterion along a regular element.
* H. Matsumura, *Commutative Ring Theory*, Theorems 22.3 and 22.5.
-/

public section

open TensorProduct LinearMap

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- If `M` is flat over `R`, then `M ⧸ x M` is flat over `R ⧸ (x)`. -/
instance Flat.quotSMulTop [Flat R M] (x : R) : Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  .of_linearEquiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective)

/-- If `M` is flat over `R`, then `M ⧸ I M` is flat over `R ⧸ I`. -/
instance Flat.quotient_smul_top [Flat R M] (I : Ideal R) :
    Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  .of_linearEquiv ((quotTensorEquivQuotSMul M I).symm.extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective)

/-! ### The local criterion -/

/-- Let `R` and `S` be Noetherian, `M` a finite `S`-module and `I` an ideal of `R` with `I S` in the
Jacobson radical of `S`. If for every `n` the kernel of `J ⊗[R] M → M` comes from
`(J ⊓ I ^ n) ⊗[R] M`, then `M` is flat over `R`: by Artin–Rees and Krull's intersection theorem. -/
private theorem Flat.of_forall_mem_range_rTensor_inclusion_inf_pow [IsNoetherianRing R]
    {S : Type*} [CommRing S] [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M] {I : Ideal R} (hIS : I.map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson)
    (hker : ∀ (n : ℕ) (J : Ideal R) (t : J ⊗[R] M), J.subtype.rTensor M t = 0 →
      t ∈ range ((Submodule.inclusion (inf_le_left : J ⊓ I ^ n ≤ J)).rTensor M)) :
    Flat R M := by
  refine Flat.iff_rTensor_injective'.mpr fun J ↦ (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  -- By Artin–Rees, `t` is divisible by every power of `I` in `J ⊗[R] M`.
  have hmem (n : ℕ) : t ∈ (I ^ n • ⊤ : Submodule R (J ⊗[R] M)) := by
    obtain ⟨u, rfl⟩ := hker (n + k) J t ht
    have hle : J ⊓ I ^ (n + k) ≤ I ^ n • J := fun c hc ↦ by
      have := hk (n + k) (Nat.le_add_left k n)
      rw [Nat.add_sub_cancel] at this
      have hc' : c ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ J :=
        ⟨by simpa [smul_eq_mul, Ideal.mul_top] using hc.2, hc.1⟩
      rw [this] at hc'
      exact Submodule.smul_mono le_rfl inf_le_right hc'
    have hcomp : Submodule.inclusion Submodule.smul_le_right ∘ₗ Submodule.inclusion hle =
        Submodule.inclusion (inf_le_left : J ⊓ I ^ (n + k) ≤ J) := by
      ext; simp
    refine range_rTensor_inclusion_smul_le (I ^ n) J ⟨(Submodule.inclusion hle).rTensor M u, ?_⟩
    rw [← rTensor_comp_apply, hcomp]
  -- Krull's intersection theorem for the finite `S`-module `M ⊗[R] J`, which `S` acts on through
  -- the left factor; it receives `t` through the symmetry of the tensor product.
  have hcomm (n : ℕ) : TensorProduct.comm R J M t ∈ (I ^ n • ⊤ : Submodule R (M ⊗[R] J)) :=
    Submodule.smul_top_le_comap_smul_top _ (TensorProduct.comm R J M).toLinearMap (hmem n)
  set IS := I.map (algebraMap R S)
  have hle (n : ℕ) : (I ^ n • ⊤ : Submodule R (M ⊗[R] J)) ≤
      (IS ^ n • (⊤ : Submodule S (M ⊗[R] J))).restrictScalars R := by
    rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson IS
    (by simpa only [Ideal.jacobson_bot] using hIS) (M := M ⊗[R] J)
  have : TensorProduct.comm R J M t ∈ ⨅ n : ℕ, IS ^ n • (⊤ : Submodule S (M ⊗[R] J)) :=
    Submodule.mem_iInf _ |>.mpr fun n ↦ hle n (hcomm n)
  simpa [hbot] using this

/-- **Local criterion for flatness**, infinitesimal form (Matsumura, Theorem 22.3, (4) ⇒ (1)). Let
`R` and `S` be Noetherian, `M` a finite `S`-module and `I` an ideal of `R` with `I S` in the
Jacobson radical of `S`. If `M ⧸ I ^ n M` is flat over `R ⧸ I ^ n` for every `n`, then `M` is flat
over `R`. -/
theorem Flat.of_forall_flat_quotient_pow [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    {I : Ideal R} (hIS : I.map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson)
    (hflat : ∀ n, Flat (R ⧸ I ^ n) (M ⧸ I ^ n • (⊤ : Submodule R M))) : Flat R M :=
  of_forall_mem_range_rTensor_inclusion_inf_pow hIS fun n _ _ ht ↦
    have := hflat n
    (I ^ n).mem_range_rTensor_inclusion_inf_of_flat ht

/-- Under the hypotheses of `Module.Flat.of_forall_flat_quotient_pow`, `M` is flat over `R` if and
only if `M ⧸ I ^ n M` is flat over `R ⧸ I ^ n` for every `n`. -/
theorem flat_iff_forall_flat_quotient_pow [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    {I : Ideal R} (hIS : I.map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson) :
    Flat R M ↔ ∀ n, Flat (R ⧸ I ^ n) (M ⧸ I ^ n • (⊤ : Submodule R M)) :=
  ⟨fun _ _ ↦ inferInstance, Flat.of_forall_flat_quotient_pow hIS⟩

section

variable {I : Ideal R} [Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))]

/-- **Local criterion for flatness** (Stacks, Tag 00MK). Let `R` and `S` be Noetherian, `M` a finite
`S`-module and `I` an ideal of `R` with `I S` in the Jacobson radical of `S`. If `I ⊗[R] M → M` is
injective, that is `Tor₁ᴿ(R ⧸ I, M) = 0`, and `M ⧸ I M` is flat over `R ⧸ I`, then `M` is flat over
`R`. -/
@[stacks 00MK "with `I S` in the Jacobson radical in place of a local homomorphism"]
theorem Flat.of_subtype_rTensor_injective [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hIS : I.map (algebraMap R S) ≤ (⊥ : Ideal S).jacobson)
    (hI : Function.Injective (I.subtype.rTensor M)) : Flat R M :=
  of_forall_mem_range_rTensor_inclusion_inf_pow hIS fun n _ _ ht ↦
    I.mem_range_rTensor_inclusion_inf_pow hI n ht

end

/-- **Flatness over the fibres** (Stacks, Tag 00MP). Let `R → S → T` be ring maps with `S` and `T`
Noetherian, let `M` be a finite `T`-module which is flat over `R`, and let `J` be an ideal of `R`
with `J T` in the Jacobson radical of `T`. If `M ⧸ J M` is flat over `S ⧸ J S`, then `M` is flat
over `S`. -/
@[stacks 00MP "with `J T` in the Jacobson radical in place of local homomorphisms"]
theorem Flat.of_flat_quotient_map {S T : Type*} [CommRing S] [IsNoetherianRing S]
    [Algebra R S] [Module S M] [IsScalarTower R S M] [CommRing T] [IsNoetherianRing T]
    [Algebra S T] [Module T M] [IsScalarTower S T M] [Module.Finite T M] [Flat R M] {J : Ideal R}
    (hJ : (J.map (algebraMap R S)).map (algebraMap S T) ≤ (⊥ : Ideal T).jacobson)
    [Flat (S ⧸ J.map (algebraMap R S)) (M ⧸ J.map (algebraMap R S) • (⊤ : Submodule S M))] :
    Flat S M :=
  of_subtype_rTensor_injective hJ (map_subtype_rTensor_injective J)

/-! ### Along a regular element -/

variable {x : R}

/-- **Local criterion for flatness** along a regular element (Stacks, Tag 00ML, for the ideal
`(x)`). Let `R` and `S` be Noetherian, `M` a finite `S`-module and `x ∈ R` with image in the
Jacobson radical of `S`. If `x` is `M`-regular and `M ⧸ x M` is flat over `R ⧸ (x)`, then `M` is
flat over `R`. -/
@[stacks 00ML "the case of a principal ideal"]
theorem Flat.of_flat_quotSMulTop [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : algebraMap R S x ∈ (⊥ : Ideal S).jacobson) (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] : Flat R M := by
  have : Flat (R ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule R M)) :=
    .of_linearEquiv ((Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤)
      ).extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
  refine of_subtype_rTensor_injective (S := S) ?_ reg.span_singleton_subtype_rTensor_injective
  simpa [Ideal.map_span, Ideal.span_singleton_le_iff_mem] using hx

/-- **Local criterion for flatness** along a regular element, for a local homomorphism `R → S` of
Noetherian local rings (Stacks, Lemma 10.99.10 (00ML), for the ideal `(x)`): if `x` lies in the
maximal ideal of `R`, is `M`-regular, and `M ⧸ x M` is flat over `R ⧸ (x)`, then the finite
`S`-module `M` is flat over `R`. -/
@[stacks 00ML "the case of a principal ideal"]
theorem Flat.of_flat_quotSMulTop_of_isLocalHom [IsLocalRing R] [IsNoetherianRing R] {S : Type*}
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : x ∈ IsLocalRing.maximalIdeal R) (reg : IsSMulRegular M x)
    [Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M)] : Flat R M :=
  of_flat_quotSMulTop (S := S) (by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact map_nonunit (algebraMap R S) x hx) reg

/-- For an `M`-regular element `x` as in `Module.Flat.of_flat_quotSMulTop`, `M ⧸ x M` is flat over
`R ⧸ (x)` if and only if `M` is flat over `R`. -/
theorem flat_quotSMulTop_iff_flat [IsNoetherianRing R] {S : Type*} [CommRing S]
    [IsNoetherianRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Module.Finite S M]
    (hx : algebraMap R S x ∈ (⊥ : Ideal S).jacobson) (reg : IsSMulRegular M x) :
    Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Flat R M :=
  ⟨fun _ ↦ Flat.of_flat_quotSMulTop hx reg, fun _ ↦ inferInstance⟩

end Module

open IsLocalRing in
/-- Let `g : R → S` and `f : S → T` be ring homomorphisms of local rings, with `S` and `T`
Noetherian and `f` local. If `f ∘ g` is flat and `g` maps the maximal ideal of `R` onto a generating
set of the maximal ideal of `S`, then `f` is flat. This is flatness over the fibres
(`Module.Flat.of_flat_quotient_map`), whose fibre condition holds because `S ⧸ 𝔪_R S` is a field.
Unlike the module version, it applies to endomorphisms such as Frobenius. -/
theorem RingHom.Flat.of_comp_of_map_maximalIdeal_eq {R S T : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [CommRing T] [IsLocalRing T]
    [IsNoetherianRing T] (g : R →+* S) (f : S →+* T) [IsLocalHom f] (hfg : (f.comp g).Flat)
    (hg : (maximalIdeal R).map g = maximalIdeal S) : f.Flat := by
  algebraize [g, f, f.comp g]
  let _ := Ideal.Quotient.field (maximalIdeal S)
  have : Module.Flat (S ⧸ maximalIdeal S) (T ⧸ maximalIdeal S • (⊤ : Submodule S T)) :=
    inferInstance
  have hg' : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := hg
  rw [← hg'] at this
  refine Module.Flat.of_flat_quotient_map (R := R) (M := T) (T := T) (J := maximalIdeal R) ?_
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact (Ideal.map_mono hg.le).trans (map_maximalIdeal_le f)

open IsLocalRing RingTheory.Sequence Pointwise

namespace Module

universe u v

/-- The induction on the length behind `Module.Flat.of_isWeaklyRegular_map_algebraMap`, stated for
all local homomorphisms in the given universes so that it applies to `R ⧸ (x) → S ⧸ x S`. -/
private theorem flat_of_isWeaklyRegular_map_algebraMap_aux (n : ℕ) :
    ∀ (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S]
      [IsLocalRing S] [IsNoetherianRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
      (rs : List R), rs.length = n → Ideal.ofList rs = maximalIdeal R →
      IsWeaklyRegular S (rs.map (algebraMap R S)) → Flat R S := by
  induction n with
  | zero =>
    intro R S _ _ _ _ _ _ _ _ rs hn hrs _
    obtain rfl := List.length_eq_zero_iff.1 hn
    have hR : IsField R := isField_iff_maximalIdeal_eq.2 (by simpa using hrs.symm)
    exact RingHom.flat_algebraMap_iff.1 (RingHom.Flat.of_isField hR _)
  | succ n ih =>
    intro R S _ _ _ _ _ _ _ _ rs hn hrs hreg
    obtain ⟨x, rs, rfl⟩ := List.exists_cons_of_length_eq_add_one hn
    rw [List.map_cons, isWeaklyRegular_cons_iff] at hreg
    obtain ⟨reg, hreg⟩ := hreg
    have hx : x ∈ maximalIdeal R := hrs ▸ Ideal.subset_span List.mem_cons_self
    set I := Ideal.span {x}
    set J := I.map (algebraMap R S)
    have hJ : J = Ideal.span {algebraMap R S x} := by
      simp only [J, I, Ideal.map_span, Set.image_singleton]
    have hJm : J ≤ maximalIdeal S := hJ ▸ (Ideal.span_singleton_le_iff_mem _).2
      (map_nonunit (algebraMap R S) x hx)
    have : Nontrivial (R ⧸ I) :=
      Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
        ((Ideal.span_singleton_le_iff_mem _).2 hx))
    have : Nontrivial (S ⧸ J) :=
      Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hJm)
    have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalRing (S ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk J) := .of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap (R ⧸ I) (S ⧸ J)) := ⟨fun a ha ↦ by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact (isUnit_of_map_unit (algebraMap R S) a
        (isUnit_of_map_unit (Ideal.Quotient.mk J) _ ha)).map _⟩
    -- The inductive hypothesis applies to `R ⧸ (x) → S ⧸ x S`.
    have hrs' : Ideal.ofList (rs.map (Ideal.Quotient.mk I)) = maximalIdeal (R ⧸ I) := by
      rw [← Ideal.map_ofList, ← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
        ← hrs, Ideal.ofList_cons, Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq]
    have eS : QuotSMulTop (algebraMap R S x) S ≃ₗ[S] S ⧸ J := Submodule.quotEquivOfEq _ _ <| by
      rw [hJ, ← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
    have hreg' : IsWeaklyRegular (S ⧸ J)
        ((rs.map (Ideal.Quotient.mk I)).map (algebraMap (R ⧸ I) (S ⧸ J))) := by
      rw [List.map_map]
      have := (isWeaklyRegular_map_algebraMap_iff (R := S) (S := S ⧸ J) (M := S ⧸ J)
        (rs.map (algebraMap R S))).2 ((eS.isWeaklyRegular_congr _).1 hreg)
      rwa [List.map_map] at this
    have : Flat (R ⧸ I) (S ⧸ J) := ih _ _ _ (by simpa using hn) hrs' hreg'
    -- Hence `S ⧸ x S` is flat over `R ⧸ (x)`, and the local criterion lifts this to `S`.
    have eR : QuotSMulTop x S ≃ₗ[R] S ⧸ J :=
      Submodule.quotEquivOfEq _ (J.restrictScalars R)
        (by rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_top_eq_map]) ≪≫ₗ
        Submodule.Quotient.restrictScalarsEquiv R J
    have : Flat (R ⧸ I) (QuotSMulTop x S) :=
      .of_linearEquiv (eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective)
    exact Flat.of_flat_quotSMulTop_of_isLocalHom (S := S) hx
      ((isSMulRegular_algebraMap_iff (A := S)).1 reg)

variable {R S : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing S]
  [IsLocalRing S] [IsNoetherianRing S]

/-- **Flatness from a regular sequence.** Let `R → S` be a local homomorphism of Noetherian local
rings. If `r₁, …, rₙ` generate the maximal ideal of `R` and their images form a weakly `S`-regular
sequence, then `S` is flat over `R`. This iterates the local criterion
`Module.Flat.of_flat_quotSMulTop_of_isLocalHom` along the sequence. -/
theorem Flat.of_isWeaklyRegular_map_algebraMap [Algebra R S] [IsLocalHom (algebraMap R S)]
    {rs : List R} (hrs : Ideal.ofList rs = maximalIdeal R)
    (hreg : IsWeaklyRegular S (rs.map (algebraMap R S))) : Flat R S :=
  flat_of_isWeaklyRegular_map_algebraMap_aux _ R S rs rfl hrs hreg

end Module

/-- **Flatness from a regular sequence**, for a local homomorphism `f : R →+* S` of Noetherian
local rings: if `r₁, …, rₙ` generate the maximal ideal of `R` and `f r₁, …, f rₙ` is a weakly
`S`-regular sequence, then `f` is flat. Unlike `Module.Flat.of_isWeaklyRegular_map_algebraMap`,
this applies to endomorphisms, such as Frobenius, without an algebra structure of `R` over
itself. -/
theorem RingHom.Flat.of_isWeaklyRegular_map {R S : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (f : R →+* S)
    [IsLocalHom f] {rs : List R} (hrs : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular S (rs.map f)) : f.Flat := by
  algebraize [f]
  exact Module.Flat.of_isWeaklyRegular_map_algebraMap (R := R) (S := S) hrs hreg
