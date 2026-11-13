/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import TauCeti.RingTheory.Henselian.IndEtale
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import TauCeti.RingTheory.Henselian.Quotient

/-!
# Recognising a henselization at a field-valued point

Let `R` be a commutative ring and `L` a field equipped with an `R`-algebra structure, determining
the prime `𝔭 = ker (R → L)` of `R`. An `R`-algebra `A` (in the universe of `R`) together with an
`R`-algebra map `ψ : A →ₐ[R] L` is a *henselization* of `R` at `R → L` (`TauCeti.IsHenselization ψ`)
if:

1. `A` is a Henselian local ring (`henselianLocalRing`),
2. `A` is ind-étale over `R` (`indEtale`), and
3. `ψ` is surjective (`surjective`), so its kernel is the maximal ideal of `A` and `ψ` identifies
   the residue field of `A` with `L` (`residueFieldEquiv`).

No local-ring hypothesis is placed on `R`: when `R` is local with residue field `κ`, taking
`L = κ` recognises the ordinary henselization of `R`, while taking `L` to be a separable closure of
`κ` recognises the strict henselization (Stacks, Definition 10.155.3 (04GQ)). Every model —
whether a colimit of pointed étale neighbourhoods or a stalk in the étale topology — can then be
compared through this predicate without reference to its construction.

The comparison rests on two theorems:

* `TauCeti.IsHenselization.existsUnique_comp_eq` (Stacks, Lemma 10.154.6 (08HR)): if `A` is any
  ind-étale `R`-algebra with an `R`-algebra map `ψ : A →ₐ[R] L` and `χ : B →ₐ[R] L` is a surjective
  `R`-algebra map out of a Henselian local `R`-algebra `B`, there is a unique `R`-algebra map
  `f : A →ₐ[R] B` satisfying `χ ∘ f = ψ`. Neither Henselianity of `A` nor surjectivity of `ψ` is
  used, so this applies both to a henselization and to each étale stage of a colimit presentation.
* `TauCeti.IsHenselization.bijective_of_comp_eq` (Stacks, Lemma 10.154.7 (08HT)): when both `ψ`
  and `χ` satisfy `IsHenselization`, every `R`-algebra map `f : A →ₐ[R] B` with `χ ∘ f = ψ` is
  bijective. Assembling the unique compatible map (`lift`) into an isomorphism via
  `AlgEquiv.ofBijective` produces the canonical `R`-algebra isomorphism `algEquiv ψ χ : A ≃ₐ[R] B`
  over `L`.

## Implementation notes

Neither `IsHenselization.henselianLocalRing` nor `IsHenselization.indEtale` can be registered as a
global typeclass instance, because `L` and `ψ` (and `R` in the first case) do not appear in the
target type. Helper lemmas whose statements mention local-ring operations such as `maximalIdeal A`
or `ResidueField A` take `[IsLocalRing A]` as a typeclass argument so callers that already carry a
local-ring instance on `A` find it automatically, while callers working with an abstract
`[h : IsHenselization ψ]` obtain `IsLocalRing A` from `h.isLocalRing`. By contrast, `IsLocalHom ψ`
mentions `ψ` directly and is registered as a global instance (`IsHenselization.isLocalHom`).

## Main declarations

* `TauCeti.IsHenselization`: recognition predicate for a henselization of `R` at a field-valued
  point `ψ : A →ₐ[R] L`.
* `TauCeti.IsHenselization.residueFieldEquiv`: the `R`-algebra isomorphism `κ(A) ≃ₐ[R] L` induced
  by `ψ`.
* `TauCeti.IsHenselization.existsUnique_comp_eq`, `TauCeti.IsHenselization.lift`: existence and
  uniqueness of compatible `R`-algebra maps from an ind-étale algebra into a Henselian local ring.
* `TauCeti.IsHenselization.bijective_of_comp_eq`, `TauCeti.IsHenselization.algEquiv`: uniqueness up
  to unique compatible isomorphism of henselizations at the same point.
* `TauCeti.IsHenselization.restrictScalars`: transitivity along an ind-étale base change `R → S`.

## References

* [Stacks Project, Definition 10.155.3 (04GQ)](https://stacks.math.columbia.edu/tag/04GQ)
* [Stacks Project, Lemma 10.154.6 (08HR)](https://stacks.math.columbia.edu/tag/08HR)
* [Stacks Project, Lemma 10.154.7 (08HT)](https://stacks.math.columbia.edu/tag/08HT)
-/

public section

open IsLocalRing

universe u v w

namespace TauCeti

/-- A *henselization* of the ring `R` at the field-valued point `R → L`, recognised by its
properties: `A` is a Henselian local ring, ind-étale over `R` (a small filtered colimit of étale
`R`-algebras), and `ψ : A → L` is surjective, so that it identifies `L` with the residue field of
`A`. Nothing is assumed of `R`: `A` is a henselization of `R` at the prime `ker (R → L)`. For `R`
local with residue field `κ`, `L = κ` gives the henselization and a separable closure `L` of `κ`
the strict henselization, Stacks, Definition 10.155.3 (04GQ); any two henselizations at the same
point are uniquely isomorphic over `L`, Stacks, Lemma 10.154.7 (08HT)
(`IsHenselization.existsUnique_comp_eq` with `IsHenselization.bijective_of_comp_eq`). -/
@[stacks 04GQ "recognised by the properties of 08HT, at any field-valued point"]
class IsHenselization {R A : Type u} {L : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field L] [Algebra R L] (ψ : A →ₐ[R] L) : Prop where
  /-- `A` is a Henselian local ring. -/
  henselianLocalRing : HenselianLocalRing A
  /-- `A` is a small filtered colimit of étale `R`-algebras. -/
  indEtale : Algebra.IndEtale R A
  /-- `ψ` is surjective, hence identifies `L` with the residue field of `A`. -/
  surjective : Function.Surjective ψ

namespace IsHenselization

section Basic

variable {R A : Type u} {L : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [Field L] [Algebra R L]

/-- The underlying ring of a henselization is a local ring. -/
theorem isLocalRing (ψ : A →ₐ[R] L) [h : IsHenselization ψ] : IsLocalRing A :=
  h.henselianLocalRing.toIsLocalRing

/-- A henselization of `R` is flat over `R`, since it is ind-étale over `R`. -/
theorem flat (ψ : A →ₐ[R] L) [h : IsHenselization ψ] : Module.Flat R A := by
  have := h.indEtale
  infer_instance

/-- The pointing map of a henselization is a local homomorphism: its kernel is the maximal ideal
of `A`. -/
instance isLocalHom (ψ : A →ₐ[R] L) [h : IsHenselization ψ] : IsLocalHom ψ := by
  have := h.isLocalRing
  refine ⟨fun a ha ↦ notMem_maximalIdeal.mp ?_⟩
  rw [← IsLocalRing.ker_eq_maximalIdeal ψ.toRingHom h.surjective, RingHom.mem_ker]
  exact ha.ne_zero

/-- An element of a henselization is a unit if and only if its image in the residue field `L` is
nonzero. -/
theorem isUnit_iff (ψ : A →ₐ[R] L) [IsHenselization ψ] (a : A) :
    IsUnit a ↔ ψ a ≠ 0 :=
  ⟨fun ha ↦ (ha.map ψ).ne_zero,
    fun ha ↦ isUnit_of_map_unit ψ a (isUnit_iff_ne_zero.mpr ha)⟩

/-- Over a local ring `R` with a local point `R → L`, every henselization at `R → L` is faithfully
flat over `R`. -/
theorem faithfullyFlat [IsLocalRing R] (ψ : A →ₐ[R] L) [IsHenselization ψ]
    [hRL : IsLocalHom (algebraMap R L)] : Module.FaithfullyFlat R A := by
  have := isLocalRing ψ
  have := flat ψ
  have : IsLocalHom (ψ.toRingHom.comp (algebraMap R A)) := ψ.comp_algebraMap.symm ▸ hRL
  have := isLocalHom_of_comp (algebraMap R A) ψ.toRingHom
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

section IsLocalRing

variable [IsLocalRing A]

/-- The kernel of the pointing map `ψ : A →ₐ[R] L` is the maximal ideal of `A`. -/
theorem ker_eq_maximalIdeal (ψ : A →ₐ[R] L) [h : IsHenselization ψ] :
    RingHom.ker ψ = maximalIdeal A :=
  IsLocalRing.ker_eq_maximalIdeal ψ.toRingHom h.surjective

/-- The maximal ideal of `A` contracts in `R` to the prime ideal `ker (R → L)` determined by the
point. -/
theorem comap_maximalIdeal (ψ : A →ₐ[R] L) [IsHenselization ψ] :
    (maximalIdeal A).comap (algebraMap R A) = RingHom.ker (algebraMap R L) := by
  rw [← ker_eq_maximalIdeal ψ]
  ext r
  simp

/-- The `R`-algebra isomorphism `κ(A) ≃ₐ[R] L` induced by the surjective map `ψ : A →ₐ[R] L`. -/
noncomputable def residueFieldEquiv (ψ : A →ₐ[R] L) [h : IsHenselization ψ] :
    ResidueField A ≃ₐ[R] L :=
  (Ideal.quotientEquivAlgOfEq R (ker_eq_maximalIdeal ψ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective h.surjective)

/-- `residueFieldEquiv ψ` sends the residue of `a` to `ψ a`. -/
@[simp]
theorem residueFieldEquiv_residue (ψ : A →ₐ[R] L) [h : IsHenselization ψ] (a : A) :
    residueFieldEquiv ψ (residue A a) = ψ a := by
  have hker : maximalIdeal A = RingHom.ker ψ := (ker_eq_maximalIdeal ψ).symm
  -- `ResidueField A` is the quotient by `maximalIdeal A` with quotient map `residue A`; rewriting
  -- with `residue_def` would alter the dependent type, so pass to the quotient form directly.
  change Ideal.quotientKerAlgEquivOfSurjective h.surjective
    (Ideal.quotientEquivAlgOfEq R hker (Ideal.Quotient.mk _ a)) = ψ a
  rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The inverse of `residueFieldEquiv ψ` sends `ψ a` to the residue of `a`. -/
@[simp]
theorem residueFieldEquiv_symm_apply (ψ : A →ₐ[R] L) [IsHenselization ψ] (a : A) :
    (residueFieldEquiv ψ).symm (ψ a) = residue A a :=
  (residueFieldEquiv ψ).symm_apply_eq.mpr (residueFieldEquiv_residue ψ a).symm

end IsLocalRing

end Basic

section Lift

/-- **Maps out of an ind-étale algebra into a henselian local ring.** If `A` is ind-étale over
`R`, `ψ : A → L` is an `R`-algebra map to a field and `χ : B → L` is a surjective `R`-algebra map
from a henselian local ring, there is exactly one `R`-algebra map `f : A → B` with `χ ∘ f = ψ`.
Stacks, Lemma 10.154.6 (08HR), in its own generality: stage by stage (Lemma 10.153.11, 08HQ, over
the localisation of `R` at `ker (R → L)`) for the prime `ker ψ` of the étale stage and the residue
map into `L ≅ κ(B)`. Neither henselianity of `A` nor surjectivity of `ψ` is needed, so the theorem
applies to every étale stage `A_i` of a henselization as well as to the henselization itself.
Without the surjectivity of `χ` there is in general no such map: `L` need not embed in `κ(B)` over
`R`. For `A` the strict henselization, `f` is `TauCeti.StrictHenselization.lift`. -/
@[stacks 08HR "for an ind-étale algebra and the residue map induced by ψ and χ"]
theorem existsUnique_comp_eq {R A : Type u} {B L : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [Algebra.IndEtale R A] [CommRing B] [Algebra R B]
    [HenselianLocalRing B] [Field L] [Algebra R L] (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L)
    (hχ : Function.Surjective χ) : ∃! f : A →ₐ[R] B, χ.comp f = ψ :=
  (HenselianLocalRing.comp_bijective_of_surjective χ hχ).existsUnique ψ

variable {R A : Type u} {B : Type v} {L : Type w} [CommRing R]
  [CommRing A] [Algebra R A] [Algebra.IndEtale R A] [CommRing B] [Algebra R B]
  [HenselianLocalRing B] [Field L] [Algebra R L]

/-- The unique `R`-algebra map `A →ₐ[R] B` from an ind-étale `R`-algebra `A` to a Henselian local
`R`-algebra `B` lifting `ψ : A →ₐ[R] L` along a surjective `R`-algebra map `χ : B →ₐ[R] L`. -/
noncomputable def lift (ψ : A →ₐ[R] L) {χ : B →ₐ[R] L} (hχ : Function.Surjective χ) :
    A →ₐ[R] B :=
  Function.surjInv (HenselianLocalRing.comp_bijective_of_surjective χ hχ).2 ψ

/-- Composing `lift ψ hχ` with `χ` recovers `ψ`. -/
@[simp]
theorem comp_lift (ψ : A →ₐ[R] L) {χ : B →ₐ[R] L} (hχ : Function.Surjective χ) :
    χ.comp (lift ψ hχ) = ψ :=
  Function.surjInv_eq (HenselianLocalRing.comp_bijective_of_surjective χ hχ).2 ψ

/-- Elementwise form of `comp_lift`. -/
@[simp]
theorem apply_lift (ψ : A →ₐ[R] L) {χ : B →ₐ[R] L} (hχ : Function.Surjective χ) (a : A) :
    χ (lift ψ hχ a) = ψ a :=
  DFunLike.congr_fun (comp_lift ψ hχ) a

/-- Every `R`-algebra map `f : A →ₐ[R] B` satisfying `χ ∘ f = ψ` agrees with `lift ψ hχ`. -/
theorem eq_lift {ψ : A →ₐ[R] L} {χ : B →ₐ[R] L} (hχ : Function.Surjective χ)
    {f : A →ₐ[R] B} (hf : χ.comp f = ψ) : f = lift ψ hχ :=
  (HenselianLocalRing.comp_bijective_of_surjective χ hχ).1 (hf.trans (comp_lift ψ hχ).symm)

/-- Lifting `ψ` along itself gives the identity map. -/
@[simp]
theorem lift_self [HenselianLocalRing A] (ψ : A →ₐ[R] L) (hψ : Function.Surjective ψ) :
    lift ψ hψ = AlgHom.id R A :=
  (eq_lift hψ (AlgHom.comp_id ψ)).symm

/-- Compatible lifts compose: lifting `ψ` to `B` and then `χ` to `C` equals lifting `ψ` directly
to `C`. -/
@[simp]
theorem lift_comp_lift {B' : Type u} {C : Type v} [CommRing B'] [Algebra R B']
    [Algebra.IndEtale R B'] [HenselianLocalRing B'] [CommRing C] [Algebra R C]
    [HenselianLocalRing C] (ψ : A →ₐ[R] L) {χ : B' →ₐ[R] L} (hχ : Function.Surjective χ)
    {ω : C →ₐ[R] L} (hω : Function.Surjective ω) :
    (lift χ hω).comp (lift ψ hχ) = lift ψ hω :=
  eq_lift hω (by rw [← AlgHom.comp_assoc, comp_lift, comp_lift])

/-- When `ψ` is a local homomorphism (in particular whenever `IsHenselization ψ` holds), the lift
`lift ψ hχ` is a local homomorphism. -/
instance isLocalHom_lift (ψ : A →ₐ[R] L) [IsLocalHom ψ] {χ : B →ₐ[R] L}
    (hχ : Function.Surjective χ) : IsLocalHom (lift ψ hχ) where
  map_nonunit a ha := isUnit_of_map_unit ψ a (by simpa using ha.map χ)

end Lift

section Uniqueness

/-- **Uniqueness of henselizations.** If `ψ : A → L` and `χ : B → L` are henselizations of `R` at
the same point, every `R`-algebra map `f : A → B` with `χ ∘ f = ψ` is bijective. With
`existsUnique_comp_eq` applied to the ind-étale `A`, which gives that exactly one such `f` exists,
this is Stacks, Lemma 10.154.7 (08HT); the comparison isomorphism is `AlgEquiv.ofBijective` of
that map, for `A` the strict henselization of `TauCeti.StrictHenselization.lift`, and no
isomorphism is chosen. -/
@[stacks 08HT "bijectivity of every compatible map"]
theorem bijective_of_comp_eq {R A B : Type u} {L : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Field L] [Algebra R L]
    (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L) [hψ : IsHenselization ψ] [hχ : IsHenselization χ]
    (f : A →ₐ[R] B) (hf : χ.comp f = ψ) : Function.Bijective f := by
  have := hψ.henselianLocalRing
  have := hψ.indEtale
  have := hχ.henselianLocalRing
  have := hχ.indEtale
  let g : B →ₐ[R] A := lift χ hψ.surjective
  have hfg : f.comp g = AlgHom.id R B :=
    (existsUnique_comp_eq χ χ hχ.surjective).unique
      (by rw [← AlgHom.comp_assoc, hf, comp_lift]) (AlgHom.comp_id χ)
  have hgf : g.comp f = AlgHom.id R A :=
    (existsUnique_comp_eq ψ ψ hψ.surjective).unique
      (by rw [← AlgHom.comp_assoc, comp_lift, hf]) (AlgHom.comp_id ψ)
  exact (AlgEquiv.ofAlgHom f g hfg hgf).bijective

variable {R A B C : Type u} {L : Type w} [CommRing R]
  [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [Field L] [Algebra R L]

/-- The canonical `R`-algebra isomorphism `A ≃ₐ[R] B` between two henselizations of `R` at the same
field-valued point `R → L`, obtained by promoting the unique compatible map `lift` via
`AlgEquiv.ofBijective`. -/
@[stacks 08HT "unique isomorphism of henselizations at the same point"]
noncomputable def algEquiv (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L)
    [hψ : IsHenselization ψ] [hχ : IsHenselization χ] : A ≃ₐ[R] B :=
  have := hψ.indEtale
  have := hχ.henselianLocalRing
  AlgEquiv.ofBijective (lift ψ hχ.surjective)
    (bijective_of_comp_eq ψ χ _ (comp_lift ψ hχ.surjective))

/-- The underlying `R`-algebra map of `algEquiv ψ χ` is `lift ψ hχ.surjective`. -/
theorem toAlgHom_algEquiv (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L)
    [hψ : IsHenselization ψ] [hχ : IsHenselization χ] :
    have := hψ.indEtale
    have := hχ.henselianLocalRing
    (algEquiv ψ χ).toAlgHom = lift ψ hχ.surjective :=
  (rfl)

/-- Composing `algEquiv ψ χ` with `χ` gives `ψ`. -/
@[simp]
theorem comp_algEquiv (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L)
    [hψ : IsHenselization ψ] [hχ : IsHenselization χ] :
    χ.comp (algEquiv ψ χ : A →ₐ[R] B) = ψ := by
  have := hψ.indEtale
  have := hχ.henselianLocalRing
  exact comp_lift ψ hχ.surjective

/-- Elementwise form of `comp_algEquiv`. -/
@[simp]
theorem apply_algEquiv (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L)
    [IsHenselization ψ] [IsHenselization χ] (a : A) :
    χ (algEquiv ψ χ a) = ψ a :=
  DFunLike.congr_fun (comp_algEquiv ψ χ) a

/-- Any `R`-algebra map `f : A →ₐ[R] B` satisfying `χ ∘ f = ψ` agrees with `algEquiv ψ χ`. -/
theorem eq_algEquiv_toAlgHom {ψ : A →ₐ[R] L} {χ : B →ₐ[R] L}
    [hψ : IsHenselization ψ] [hχ : IsHenselization χ] {f : A →ₐ[R] B} (hf : χ.comp f = ψ) :
    f = (algEquiv ψ χ).toAlgHom := by
  have := hψ.indEtale
  have := hχ.henselianLocalRing
  exact eq_lift hχ.surjective hf

/-- Any `R`-algebra isomorphism `e : A ≃ₐ[R] B` satisfying `χ ∘ e = ψ` equals `algEquiv ψ χ`. -/
theorem eq_algEquiv {ψ : A →ₐ[R] L} {χ : B →ₐ[R] L}
    [IsHenselization ψ] [IsHenselization χ] {e : A ≃ₐ[R] B} (he : χ.comp e.toAlgHom = ψ) :
    e = algEquiv ψ χ :=
  AlgEquiv.ext fun a ↦ DFunLike.congr_fun (eq_algEquiv_toAlgHom he) a

/-- Comparing a henselization with itself gives the identity isomorphism. -/
@[simp]
theorem algEquiv_refl (ψ : A →ₐ[R] L) [IsHenselization ψ] :
    algEquiv ψ ψ = AlgEquiv.refl :=
  (eq_algEquiv (AlgHom.comp_id ψ)).symm

/-- Reversing the order of two henselizations inverts their comparison isomorphism. -/
@[simp]
theorem algEquiv_symm (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L)
    [IsHenselization ψ] [IsHenselization χ] :
    (algEquiv ψ χ).symm = algEquiv χ ψ :=
  eq_algEquiv (AlgHom.ext fun b ↦ by
    simpa using (apply_algEquiv ψ χ ((algEquiv ψ χ).symm b)).symm)

/-- Comparison isomorphisms of henselizations compose transitively. -/
@[simp]
theorem algEquiv_trans (ψ : A →ₐ[R] L) (χ : B →ₐ[R] L) (ω : C →ₐ[R] L)
    [IsHenselization ψ] [IsHenselization χ] [IsHenselization ω] :
    (algEquiv ψ χ).trans (algEquiv χ ω) = algEquiv ψ ω :=
  eq_algEquiv (AlgHom.ext fun a ↦ by simp)

end Uniqueness

section Permanence

/-- A Henselian local ring `R` equipped with a surjective `R`-algebra map `ψ : R →ₐ[R] L` onto a
field is already its own henselization at `ψ`. -/
theorem of_surjective_of_henselianLocalRing {R : Type u} {L : Type*} [CommRing R]
    [HenselianLocalRing R] [Field L] [Algebra R L] (ψ : R →ₐ[R] L) (hψ : Function.Surjective ψ) :
    IsHenselization ψ where
  henselianLocalRing := inferInstance
  indEtale := inferInstance
  surjective := hψ

/-- A Henselian local ring `R` is its own henselization at the residue map `R →ₐ[R] κ(R)`. -/
instance isHenselization_toResidueField (R : Type u) [CommRing R] [HenselianLocalRing R] :
    IsHenselization (Algebra.ofId R (ResidueField R)) :=
  of_surjective_of_henselianLocalRing _ residue_surjective

/-- A field `K` is its own henselization at the identity map `K →ₐ[K] K`. -/
instance isHenselization_id (K : Type u) [Field K] : IsHenselization (AlgHom.id K K) :=
  of_surjective_of_henselianLocalRing _ Function.surjective_id

/-- Transport `IsHenselization` along an `R`-algebra isomorphism `e : A ≃ₐ[R] B`. -/
theorem of_algEquiv {R A B : Type u} {L : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Field L] [Algebra R L] {ψ : A →ₐ[R] L} [h : IsHenselization ψ]
    (e : A ≃ₐ[R] B) : IsHenselization (ψ.comp e.symm.toAlgHom) := by
  have := h.henselianLocalRing
  have := h.indEtale
  have : Nontrivial B := e.symm.toEquiv.nontrivial
  exact
    { henselianLocalRing := e.toRingEquiv.toRingHom.henselianLocalRing_of_surjective e.surjective
      indEtale := Algebra.IndEtale.of_equiv e
      surjective := h.surjective.comp e.symm.surjective }

/-- Post-composing the pointing map with an `R`-algebra isomorphism of fields preserves
`IsHenselization`. -/
theorem comp_algEquiv_iff {R A : Type u} {L L' : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Field L] [Algebra R L] [Field L'] [Algebra R L'] (e : L ≃ₐ[R] L') (ψ : A →ₐ[R] L) :
    IsHenselization (e.toAlgHom.comp ψ) ↔ IsHenselization ψ :=
  ⟨fun h ↦ ⟨h.henselianLocalRing, h.indEtale, fun x ↦ by
      obtain ⟨a, ha⟩ := h.surjective (e x)
      exact ⟨a, e.injective ha⟩⟩,
    fun h ↦ ⟨h.henselianLocalRing, h.indEtale, e.surjective.comp h.surjective⟩⟩

/-- **Transitivity along ind-étale extensions.** If `S` is ind-étale over `R` (for instance a
localization of `R` at a prime) and `ψ : A →ₐ[S] L` is a henselization of `S`, then `ψ` restricted
to `R` is a henselization of `R`. -/
theorem restrictScalars (R : Type u) {S A : Type u} {L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IndEtale R S] [CommRing A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Field L] [Algebra R L] [Algebra S L] [IsScalarTower R S L]
    {ψ : A →ₐ[S] L} [h : IsHenselization ψ] :
    IsHenselization (ψ.restrictScalars R) := by
  have := h.indEtale
  exact
    { henselianLocalRing := h.henselianLocalRing
      indEtale := Algebra.IndEtale.comp (R := R) (S := S) A
      surjective := h.surjective }

end Permanence

-- Sanity check: a field is its own henselization at the identity map.
example (K : Type u) [Field K] : IsHenselization (AlgHom.id K K) := inferInstance

-- Sanity check: for a prime `p`, `ZMod p` is a Henselian local ring and `ZMod p → ZMod p` is
-- surjective, yet it is not a henselization of `ℤ` because `ZMod p` is not flat over `ℤ`.
example (p : ℕ) [hp : Fact p.Prime] :
    ¬ IsHenselization (IsScalarTower.toAlgHom ℤ (ZMod p) (ZMod p)) := by
  intro h
  have := h.flat
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := ZMod p)
    (mem_nonZeroDivisors_of_ne_zero hp0)
  exact one_ne_zero (hreg (by simp))

end IsHenselization

end TauCeti
