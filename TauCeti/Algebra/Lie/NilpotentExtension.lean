/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Engel
public import TauCeti.Algebra.Lie.Nilradical

/-!
# Extending a nilpotent action by a normalizing element

Let `M` be a Lie module over `L`, let `H` be a Lie subalgebra of `L` acting nilpotently on `M`, and
let `y : L` normalize `H` and act nilpotently on `M`.  This file proves that the Lie subalgebra
spanned by `H` and `y` again acts nilpotently on `M`, so that in particular every element
`t • y + h` acts nilpotently.

The subalgebra in question is `LieSubalgebra.supSpanSingleton`, whose underlying submodule is
`R ∙ y ⊔ H.toSubmodule`; it is a Lie subalgebra exactly because `y` normalizes `H`.  Mathlib builds
the same submodule anonymously inside the proof of Engel's theorem, and supplies the two facts that
do the work here: `LieSubalgebra.lie_mem_sup_of_mem_normalizer` closes it under the bracket, and
`LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop` upgrades nilpotency of an ideal `I` of a Lie
algebra `K` to nilpotency of `K` as soon as `K = R ∙ x ⊔ I` with `x` acting nilpotently.  The step
taken here is that `H` is an ideal of `H.supSpanSingleton hy`, which is exactly the situation that
theorem describes.

Note that no Noetherian or finiteness hypothesis is needed for the subalgebra statement: it is a
statement about lower central series, not an application of Engel's theorem.  Engel's theorem enters
only in the variants whose hypothesis on `H` is the pointwise one, `∀ x ∈ H, IsNilpotent (toEnd x)`,
and those carry `[IsNoetherian R M]`.

The `H`-receiver statements live in the root `LieSubalgebra` namespace, where dot notation on that
Mathlib type elaborates, as do the corresponding statements in `TauCeti.Algebra.Lie.Nilradical`.

## Main definitions

* `LieSubalgebra.supSpanSingleton`: the Lie subalgebra spanned by a Lie subalgebra `H` together
  with an element of its normalizer, identified with `LieSubalgebra.lieSpan` of the two in
  `LieSubalgebra.supSpanSingleton_eq_lieSpan`.

## Main statements

* `LieSubalgebra.isNilpotent_supSpanSingleton`: **the nilpotent-extension lemma**.  If `H` acts
  nilpotently on `M` and a normalizing element `y` acts nilpotently on `M`, then
  `H.supSpanSingleton hy` acts nilpotently on `M`.
* `LieSubalgebra.isNilpotent_toEnd_of_mem_supSpanSingleton` and
  `LieSubalgebra.isNilpotent_toEnd_of_mem_supSpanSingleton_of_forall`: the pointwise readings, the
  second one taking the pointwise hypothesis on `H` as well.
* `LieIdeal.isNilpotent_toEnd_of_mem_span_singleton_sup`: the special case of an ideal, where the
  normalizing hypothesis is automatic and the conclusion can be read off the submodule
  `R ∙ y ⊔ I.toSubmodule` directly.
* `TauCeti.LieAlgebra.isNilpotent_ad_of_mem_span_singleton_sup_nilradical`: the adjoint
  specialization, that `t • y + n` is `ad`-nilpotent for `n` in the nilradical and `y`
  `ad`-nilpotent.

## References

* G. Hochschild, *An addition to Ado's theorem*, Proc. Amer. Math. Soc. 5 (1954), 367-373.
* [W. Fulton and J. Harris, *Representation Theory: A First Course*][fulton-harris], Appendix E.
-/

public section

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (H : LieSubalgebra R L) {y : L} (hy : y ∈ H.normalizer)

/-- The Lie subalgebra spanned by a Lie subalgebra `H` and an element `y` of its normalizer: its
underlying submodule is `R ∙ y ⊔ H.toSubmodule`, which is closed under the bracket precisely because
`y` normalizes `H`. -/
def supSpanSingleton : LieSubalgebra R L :=
  { R ∙ y ⊔ H.toSubmodule with
    lie_mem' := fun {_ _} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hy }

@[simp]
theorem toSubmodule_supSpanSingleton :
    (H.supSpanSingleton hy).toSubmodule = R ∙ y ⊔ H.toSubmodule :=
  (rfl)

@[simp]
theorem mem_supSpanSingleton {z : L} :
    z ∈ H.supSpanSingleton hy ↔ z ∈ R ∙ y ⊔ H.toSubmodule :=
  Iff.rfl

theorem mem_supSpanSingleton_iff_exists {z : L} :
    z ∈ H.supSpanSingleton hy ↔ ∃ t : R, ∃ h ∈ H, z = t • y + h := by
  rw [mem_supSpanSingleton, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨t, v, hv, rfl⟩
  · rintro ⟨t, h, hh, rfl⟩
    exact ⟨t • y, Submodule.smul_mem _ t (Submodule.mem_span_singleton_self y), h, hh, rfl⟩

theorem self_mem_supSpanSingleton : y ∈ H.supSpanSingleton hy :=
  Submodule.mem_sup_left (Submodule.mem_span_singleton_self y)

theorem le_supSpanSingleton : H ≤ H.supSpanSingleton hy :=
  fun _ hx => Submodule.mem_sup_right hx

theorem supSpanSingleton_le_normalizer : H.supSpanSingleton hy ≤ H.normalizer :=
  sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hy)
    (fun _ hx => H.le_normalizer hx)

theorem supSpanSingleton_le {K : LieSubalgebra R L} (hHK : H ≤ K) (hyK : y ∈ K) :
    H.supSpanSingleton hy ≤ K :=
  sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hyK) hHK

/-- `H.supSpanSingleton hy` really is the Lie subalgebra generated by `H` together with `y`: taking
the sum of submodules is enough, because `y` normalizes `H`. -/
theorem supSpanSingleton_eq_lieSpan :
    H.supSpanSingleton hy = LieSubalgebra.lieSpan R L (insert y (H : Set L)) := by
  refine le_antisymm ?_ (LieSubalgebra.lieSpan_le.mpr ?_)
  · refine H.supSpanSingleton_le hy (fun z hz => ?_) ?_
    · exact LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ hz)
    · exact LieSubalgebra.subset_lieSpan (Set.mem_insert _ _)
  · rintro z (rfl | hz)
    · exact H.self_mem_supSpanSingleton hy
    · exact H.le_supSpanSingleton hy hz

/-- Adjoining an element that `H` already contains changes nothing. -/
@[simp]
theorem supSpanSingleton_eq_self (hyH : y ∈ H) : H.supSpanSingleton hy = H :=
  le_antisymm (H.supSpanSingleton_le hy le_rfl hyH) (H.le_supSpanSingleton hy)

/-- **The nilpotent-extension lemma.**  If a Lie subalgebra `H` acts nilpotently on `M`, and an
element `y` normalizing `H` acts nilpotently on `M`, then the Lie subalgebra spanned by `H` and `y`
acts nilpotently on `M`. -/
theorem isNilpotent_supSpanSingleton [LieModule.IsNilpotent H M]
    (hyM : IsNilpotent (LieModule.toEnd R L M y)) :
    LieModule.IsNilpotent (H.supSpanSingleton hy) M := by
  have hHK : H ≤ H.supSpanSingleton hy := H.le_supSpanSingleton hy
  have hyK : y ∈ H.supSpanSingleton hy := H.self_mem_supSpanSingleton hy
  obtain ⟨I, hI⟩ :=
    LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer hHK (H.supSpanSingleton_le_normalizer hy)
  have hI₂ :
      R ∙ (⟨y, hyK⟩ : H.supSpanSingleton hy) ⊔ LieSubmodule.toSubmodule I = ⊤ := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule R (H.supSpanSingleton hy) I, hI]
    apply Submodule.map_injective_of_injective
      ((H.supSpanSingleton hy : Submodule R L).injective_subtype)
    simp only [LieSubalgebra.coe_ofLe, Submodule.map_sup, Submodule.map_subtype_range_inclusion,
      Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_subtype_span_singleton]
    rfl
  have hIM : LieModule.IsNilpotent I M :=
    (Equiv.lieModule_isNilpotent_iff
        ((LieSubalgebra.equivOfLe hHK).trans
          (LieEquiv.ofEq _ _ ((LieSubalgebra.coe_set_eq _ _).mpr hI.symm)))
        (1 : M ≃ₗ[R] M) fun _ _ => rfl).mp ‹_›
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop hI₂ hyM hIM

/-- Every element of the Lie subalgebra spanned by `H` and a normalizing element `y` acts
nilpotently on `M`, as soon as `H` does and `y` does. -/
theorem isNilpotent_toEnd_of_mem_supSpanSingleton [LieModule.IsNilpotent H M]
    (hyM : IsNilpotent (LieModule.toEnd R L M y)) {z : L} (hz : z ∈ H.supSpanSingleton hy) :
    IsNilpotent (LieModule.toEnd R L M z) := by
  have := H.isNilpotent_supSpanSingleton hy hyM
  exact LieModule.isNilpotent_toEnd_of_isNilpotent R (H.supSpanSingleton hy) M ⟨z, hz⟩

/-- The pointwise form of the nilpotent-extension lemma: if every element of `H` acts nilpotently on
a Noetherian module `M`, and so does a normalizing element `y`, then so does every element of the
Lie subalgebra spanned by `H` and `y`.  Engel's theorem turns the hypothesis on `H` into nilpotency
of the action, which is what `LieSubalgebra.isNilpotent_toEnd_of_mem_supSpanSingleton` consumes. -/
theorem isNilpotent_toEnd_of_mem_supSpanSingleton_of_forall [IsNoetherian R M]
    (hH : ∀ x ∈ H, IsNilpotent (LieModule.toEnd R L M x))
    (hyM : IsNilpotent (LieModule.toEnd R L M y)) {z : L} (hz : z ∈ H.supSpanSingleton hy) :
    IsNilpotent (LieModule.toEnd R L M z) := by
  have : LieModule.IsNilpotent H M :=
    (LieModule.isNilpotent_iff_forall' (R := R)).mpr fun x => hH x x.2
  exact H.isNilpotent_toEnd_of_mem_supSpanSingleton hy hyM hz

end LieSubalgebra

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Every element of `L` normalizes an ideal of `L`. -/
theorem mem_normalizer_toLieSubalgebra (I : LieIdeal R L) (y : L) :
    y ∈ (I : LieSubalgebra R L).normalizer :=
  (LieSubalgebra.mem_normalizer_iff _ y).mpr fun x hx =>
    (mem_toLieSubalgebra R L I _).mpr <|
      lie_mem_right R L I y x <| (mem_toLieSubalgebra R L I x).mp hx

/-- The nilpotent-extension lemma for an **ideal** `I` of `L`: the normalizing hypothesis is
automatic, and the elements covered by the conclusion are exactly those of the submodule
`R ∙ y ⊔ I.toSubmodule`, that is, the elements `t • y + x` with `x ∈ I`. -/
theorem isNilpotent_toEnd_of_mem_span_singleton_sup [IsNoetherian R M] (I : LieIdeal R L)
    (hI : ∀ x ∈ I, IsNilpotent (LieModule.toEnd R L M x)) {y : L}
    (hy : IsNilpotent (LieModule.toEnd R L M y)) {z : L}
    (hz : z ∈ (R ∙ y) ⊔ LieSubmodule.toSubmodule I) :
    IsNilpotent (LieModule.toEnd R L M z) :=
  (I : LieSubalgebra R L).isNilpotent_toEnd_of_mem_supSpanSingleton_of_forall
    (mem_normalizer_toLieSubalgebra I y)
    (fun x hx => hI x ((mem_toLieSubalgebra R L I x).mp hx)) hy hz

end LieIdeal

namespace TauCeti.LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The adjoint specialization of the nilpotent-extension lemma: if `y` is `ad`-nilpotent, then so
is every element `t • y + n` with `n` in the nilradical.  Every element of the nilradical is
`ad`-nilpotent, so the hypothesis of `LieIdeal.isNilpotent_toEnd_of_mem_span_singleton_sup` on the
ideal is automatic here. -/
theorem isNilpotent_ad_of_mem_span_singleton_sup_nilradical [IsNoetherian R L] {y : L}
    (hy : IsNilpotent (_root_.LieAlgebra.ad R L y)) {z : L}
    (hz : z ∈ (R ∙ y) ⊔ LieSubmodule.toSubmodule (nilradical R L)) :
    IsNilpotent (_root_.LieAlgebra.ad R L z) :=
  LieIdeal.isNilpotent_toEnd_of_mem_span_singleton_sup (nilradical R L)
    (fun _ hx => isNilpotent_ad_of_mem_nilradical hx) hy hz

end TauCeti.LieAlgebra
