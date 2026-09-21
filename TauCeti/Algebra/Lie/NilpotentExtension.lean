/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Engel
public import TauCeti.Algebra.Lie.Nilradical

/-!
# Extending a nilpotent action by a normalizing element

Let `M` be a Lie module over `L`, let `H` be a Lie subalgebra of `L` acting nilpotently on `M`, and
let `y : L` normalize `H` and act nilpotently on `M`.  This file proves that the Lie subalgebra
spanned by `y` and `H` again acts nilpotently on `M`, so that in particular every element
`t • y + h` acts nilpotently.

The subalgebra in question is `LieSubalgebra.spanSingletonSup`, whose underlying submodule is
`R ∙ y ⊔ H.toSubmodule`; it is a Lie subalgebra exactly because `y` normalizes `H`.  Mathlib builds
the same submodule anonymously inside the proof of
`LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer` in `Mathlib/Algebra/Lie/Engel.lean`,
which both the construction here and the `⊤`-membership computation inside
`LieSubalgebra.lieModule_isNilpotent_spanSingletonSup` follow closely.  That proof also supplies the
two facts that do the work: `LieSubalgebra.lie_mem_sup_of_mem_normalizer` closes the submodule under
the bracket, and `LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop` upgrades nilpotency of `M` as a
module over an ideal `I` of a Lie algebra `K` to nilpotency of `M` as a module over `K`, as soon as
`K = R ∙ x ⊔ I` with `x` acting nilpotently on `M`.  The step taken here is that `H` is an ideal of
`H.spanSingletonSup hy`, which is exactly the situation that theorem describes.

Note that no Noetherian or finiteness hypothesis is needed for the subalgebra statement: it is a
statement about lower central series, not an application of Engel's theorem.  Engel's theorem enters
only in the variants whose hypothesis on `H` is the pointwise one, `∀ x ∈ H, IsNilpotent (toEnd x)`,
and those carry `[IsNoetherian R M]`.

The `H`-receiver statements live in the root `LieSubalgebra` namespace, where dot notation on that
Mathlib type elaborates, as do the corresponding statements in `TauCeti.Algebra.Lie.Nilradical`.

## Main definitions

* `LieSubalgebra.spanSingletonSup`: the Lie subalgebra spanned by an element of the normalizer of a
  Lie subalgebra `H` together with `H`, identified with `LieSubalgebra.lieSpan` of the two in
  `LieSubalgebra.spanSingletonSup_eq_lieSpan`.

## Main statements

* `LieSubalgebra.lieModule_isNilpotent_spanSingletonSup`: **the nilpotent-extension lemma**.  If `H`
  acts nilpotently on `M` and a normalizing element `y` acts nilpotently on `M`, then
  `H.spanSingletonSup hy` acts nilpotently on `M`.
* `LieSubalgebra.isNilpotent_toEnd_of_mem_spanSingletonSup` and
  `LieSubalgebra.isNilpotent_toEnd_of_mem_spanSingletonSup_of_forall`: the pointwise readings, the
  second one taking the pointwise hypothesis on `H` as well.
* `LieIdeal.isNilpotent_toEnd_of_mem_span_singleton_sup`: the special case of an ideal, where the
  normalizing hypothesis is automatic and the conclusion can be read off the submodule
  `R ∙ y ⊔ I.toSubmodule` directly, together with its `t • y + x` reading
  `LieIdeal.isNilpotent_toEnd_smul_add_of_mem`.
* `TauCeti.LieAlgebra.isNilpotent_ad_of_mem_span_singleton_sup_nilradical` and
  `TauCeti.LieAlgebra.isNilpotent_ad_smul_add_of_mem_nilradical`: the adjoint specialization, that
  `t • y + n` is `ad`-nilpotent for `n` in the nilradical and `y` `ad`-nilpotent.

## References

* G. Hochschild, *An addition to Ado's theorem*, Proc. Amer. Math. Soc. 17 (1966), 531-533.
* [W. Fulton and J. Harris, *Representation Theory: A First Course*][fulton-harris1991],
  Appendix E, §E.2.
-/

public section

namespace LieSubalgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (H : LieSubalgebra R L) {y : L} (hy : y ∈ H.normalizer)

/-- The Lie subalgebra spanned by an element `y` of the normalizer of a Lie subalgebra `H` together
with `H`: its underlying submodule is `R ∙ y ⊔ H.toSubmodule`, which is closed under the bracket
precisely because `y` normalizes `H`. -/
def spanSingletonSup : LieSubalgebra R L :=
  { R ∙ y ⊔ H.toSubmodule with
    lie_mem' := fun {_ _} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hy }

@[simp]
theorem toSubmodule_spanSingletonSup :
    (H.spanSingletonSup hy).toSubmodule = R ∙ y ⊔ H.toSubmodule :=
  (rfl)

/-- Membership in `H.spanSingletonSup hy` unfolds to membership in `R ∙ y ⊔ H.toSubmodule`.  This is
the bridge that every other lemma in this file goes through; it is deliberately *not* a `simp`
lemma, so that `simp` leaves the `spanSingletonSup` head in place for the characteristic lemmas
below. -/
theorem mem_spanSingletonSup {z : L} :
    z ∈ H.spanSingletonSup hy ↔ z ∈ R ∙ y ⊔ H.toSubmodule :=
  (Iff.rfl)

theorem mem_spanSingletonSup_iff_exists {z : L} :
    z ∈ H.spanSingletonSup hy ↔ ∃ t : R, ∃ h ∈ H, z = t • y + h := by
  rw [mem_spanSingletonSup, Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨t, v, hv, rfl⟩
  · rintro ⟨t, h, hh, rfl⟩
    exact ⟨t • y, Submodule.smul_mem _ t (Submodule.mem_span_singleton_self y), h, hh, rfl⟩

theorem self_mem_spanSingletonSup : y ∈ H.spanSingletonSup hy :=
  (H.mem_spanSingletonSup hy).mpr (Submodule.mem_sup_left (Submodule.mem_span_singleton_self y))

theorem le_spanSingletonSup : H ≤ H.spanSingletonSup hy :=
  fun _ hx => (H.mem_spanSingletonSup hy).mpr (Submodule.mem_sup_right hx)

theorem spanSingletonSup_le {K : LieSubalgebra R L} (hHK : H ≤ K) (hyK : y ∈ K) :
    H.spanSingletonSup hy ≤ K := fun _ hz => by
  obtain ⟨t, h, hh, rfl⟩ := (H.mem_spanSingletonSup_iff_exists hy).mp hz
  exact K.add_mem (K.smul_mem t hyK) (hHK hh)

theorem spanSingletonSup_le_normalizer : H.spanSingletonSup hy ≤ H.normalizer :=
  H.spanSingletonSup_le hy H.le_normalizer hy

/-- `H.spanSingletonSup hy` really is the Lie subalgebra generated by `H` together with `y`: taking
the sum of submodules is enough, because `y` normalizes `H`. -/
theorem spanSingletonSup_eq_lieSpan :
    H.spanSingletonSup hy = LieSubalgebra.lieSpan R L (insert y (H : Set L)) := by
  refine le_antisymm ?_ (LieSubalgebra.lieSpan_le.mpr ?_)
  · refine H.spanSingletonSup_le hy (fun z hz => ?_) ?_
    · exact LieSubalgebra.subset_lieSpan (Set.mem_insert_of_mem _ hz)
    · exact LieSubalgebra.subset_lieSpan (Set.mem_insert _ _)
  · rintro z (rfl | hz)
    · exact H.self_mem_spanSingletonSup hy
    · exact H.le_spanSingletonSup hy hz

/-- Adjoining an element that `H` already contains changes nothing. -/
@[simp]
theorem spanSingletonSup_eq_self (hyH : y ∈ H) : H.spanSingletonSup hy = H :=
  le_antisymm (H.spanSingletonSup_le hy le_rfl hyH) (H.le_spanSingletonSup hy)

/-- **The nilpotent-extension lemma.**  If a Lie subalgebra `H` acts nilpotently on `M`, and an
element `y` normalizing `H` acts nilpotently on `M`, then the Lie subalgebra spanned by `y` and `H`
acts nilpotently on `M`. -/
theorem lieModule_isNilpotent_spanSingletonSup [LieModule.IsNilpotent H M]
    (hyM : IsNilpotent (LieModule.toEnd R L M y)) :
    LieModule.IsNilpotent (H.spanSingletonSup hy) M := by
  have hHK : H ≤ H.spanSingletonSup hy := H.le_spanSingletonSup hy
  have hyK : y ∈ H.spanSingletonSup hy := H.self_mem_spanSingletonSup hy
  obtain ⟨I, hI⟩ :=
    LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer hHK (H.spanSingletonSup_le_normalizer hy)
  -- `LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop` needs the spanning equation *inside* the
  -- larger subalgebra.  Both sides are submodules of `↥(H.spanSingletonSup hy)`, and the subtype
  -- inclusion of that submodule is injective, so it suffices to check the equation after pushing it
  -- forward into `L`, where it is exactly `toSubmodule_spanSingletonSup`.
  have hI₂ :
      R ∙ (⟨y, hyK⟩ : H.spanSingletonSup hy) ⊔ LieSubmodule.toSubmodule I = ⊤ := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule R (H.spanSingletonSup hy) I, hI]
    apply Submodule.map_injective_of_injective
      ((H.spanSingletonSup hy : Submodule R L).injective_subtype)
    simp only [LieSubalgebra.coe_ofLe, Submodule.map_sup, Submodule.map_subtype_range_inclusion,
      Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_subtype_span_singleton]
    exact (H.toSubmodule_spanSingletonSup hy).symm
  have hIM : LieModule.IsNilpotent I M :=
    (Equiv.lieModule_isNilpotent_iff
        ((LieSubalgebra.equivOfLe hHK).trans
          (LieEquiv.ofEq _ _ ((LieSubalgebra.coe_set_eq _ _).mpr hI.symm)))
        (1 : M ≃ₗ[R] M) fun _ _ => rfl).mp ‹_›
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop hI₂ hyM hIM

/-- Every element of the Lie subalgebra spanned by a normalizing element `y` and `H` acts
nilpotently on `M`, as soon as `H` does and `y` does. -/
theorem isNilpotent_toEnd_of_mem_spanSingletonSup [LieModule.IsNilpotent H M]
    (hyM : IsNilpotent (LieModule.toEnd R L M y)) {z : L} (hz : z ∈ H.spanSingletonSup hy) :
    IsNilpotent (LieModule.toEnd R L M z) := by
  have : LieModule.IsNilpotent (H.spanSingletonSup hy) M :=
    H.lieModule_isNilpotent_spanSingletonSup hy hyM
  -- the action of `⟨z, hz⟩` through the subalgebra is the action of `z` through `L`
  rw [← LieSubalgebra.toEnd_mk R L M (H.spanSingletonSup hy) hz]
  exact LieModule.isNilpotent_toEnd_of_isNilpotent R (H.spanSingletonSup hy) M ⟨z, hz⟩

/-- The pointwise form of the nilpotent-extension lemma: if every element of `H` acts nilpotently on
a Noetherian module `M`, and so does a normalizing element `y`, then so does every element of the
Lie subalgebra spanned by `y` and `H`.  Engel's theorem turns the hypothesis on `H` into nilpotency
of the action, which is what `LieSubalgebra.isNilpotent_toEnd_of_mem_spanSingletonSup` consumes. -/
theorem isNilpotent_toEnd_of_mem_spanSingletonSup_of_forall [IsNoetherian R M]
    (hH : ∀ x ∈ H, IsNilpotent (LieModule.toEnd R L M x))
    (hyM : IsNilpotent (LieModule.toEnd R L M y)) {z : L} (hz : z ∈ H.spanSingletonSup hy) :
    IsNilpotent (LieModule.toEnd R L M z) := by
  have : LieModule.IsNilpotent H M :=
    (LieModule.isNilpotent_iff_forall' (R := R)).mpr fun x => hH x x.2
  exact H.isNilpotent_toEnd_of_mem_spanSingletonSup hy hyM hz

end LieSubalgebra

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
variable {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The nilpotent-extension lemma for an **ideal** `I` of `L`: the normalizing hypothesis is
automatic, and the elements covered by the conclusion are exactly those of the submodule
`R ∙ y ⊔ I.toSubmodule`, that is, the elements `t • y + x` with `x ∈ I`. -/
theorem isNilpotent_toEnd_of_mem_span_singleton_sup [IsNoetherian R M] (I : LieIdeal R L)
    (hI : ∀ x ∈ I, IsNilpotent (LieModule.toEnd R L M x)) {y : L}
    (hy : IsNilpotent (LieModule.toEnd R L M y)) {z : L}
    (hz : z ∈ (R ∙ y) ⊔ LieSubmodule.toSubmodule I) :
    IsNilpotent (LieModule.toEnd R L M z) := by
  -- every element of `L` normalizes an ideal: `LieIdeal.normalizer_eq_top`
  have hyN : y ∈ (I : LieSubalgebra R L).normalizer := by
    rw [I.normalizer_eq_top]
    exact LieSubalgebra.mem_top y
  have hz' : z ∈ (I : LieSubalgebra R L).spanSingletonSup hyN := by
    rw [LieSubalgebra.mem_spanSingletonSup, LieIdeal.toLieSubalgebra_toSubmodule R L I]
    exact hz
  exact (I : LieSubalgebra R L).isNilpotent_toEnd_of_mem_spanSingletonSup_of_forall hyN
    (fun x hx => hI x ((mem_toLieSubalgebra R L I x).mp hx)) hy hz'

/-- The `t • y + x` reading of `LieIdeal.isNilpotent_toEnd_of_mem_span_singleton_sup`: for an ideal
`I` all of whose elements act nilpotently on `M`, and `y` acting nilpotently on `M`, every
`t • y + x` with `x ∈ I` acts nilpotently on `M`. -/
theorem isNilpotent_toEnd_smul_add_of_mem [IsNoetherian R M] (I : LieIdeal R L)
    (hI : ∀ x ∈ I, IsNilpotent (LieModule.toEnd R L M x)) {y : L}
    (hy : IsNilpotent (LieModule.toEnd R L M y)) (t : R) {x : L} (hx : x ∈ I) :
    IsNilpotent (LieModule.toEnd R L M (t • y + x)) :=
  I.isNilpotent_toEnd_of_mem_span_singleton_sup hI hy <| Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.smul_mem _ t (Submodule.mem_span_singleton_self y)))
    (Submodule.mem_sup_right ((LieSubmodule.mem_toSubmodule I).mpr hx))

end LieIdeal

namespace TauCeti.LieAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The adjoint action is the action of `L` on itself as a Lie module. -/
private theorem ad_eq_toEnd (x : L) :
    _root_.LieAlgebra.ad R L x = LieModule.toEnd R L L x :=
  LinearMap.ext fun _ => rfl

/-- The adjoint specialization of the nilpotent-extension lemma: if `y` is `ad`-nilpotent, then so
is every element of `R ∙ y ⊔ nilradical R L`.  Every element of the nilradical is `ad`-nilpotent, so
the hypothesis of `LieIdeal.isNilpotent_toEnd_of_mem_span_singleton_sup` on the ideal is automatic
here. -/
theorem isNilpotent_ad_of_mem_span_singleton_sup_nilradical [IsNoetherian R L] {y : L}
    (hy : IsNilpotent (_root_.LieAlgebra.ad R L y)) {z : L}
    (hz : z ∈ (R ∙ y) ⊔ LieSubmodule.toSubmodule (nilradical R L)) :
    IsNilpotent (_root_.LieAlgebra.ad R L z) := by
  have hN : ∀ x ∈ nilradical R L, IsNilpotent (LieModule.toEnd R L L x) := fun x hx => by
    rw [← ad_eq_toEnd (R := R) x]
    exact isNilpotent_ad_of_mem_nilradical hx
  have hy' : IsNilpotent (LieModule.toEnd R L L y) := by
    rw [← ad_eq_toEnd (R := R) y]
    exact hy
  rw [ad_eq_toEnd (R := R) z]
  exact LieIdeal.isNilpotent_toEnd_of_mem_span_singleton_sup (nilradical R L) hN hy' hz

/-- The `t • y + n` reading of `isNilpotent_ad_of_mem_span_singleton_sup_nilradical`: if `y` is
`ad`-nilpotent, then so is `t • y + n` for every `n` in the nilradical. -/
theorem isNilpotent_ad_smul_add_of_mem_nilradical [IsNoetherian R L] {y : L}
    (hy : IsNilpotent (_root_.LieAlgebra.ad R L y)) (t : R) {n : L} (hn : n ∈ nilradical R L) :
    IsNilpotent (_root_.LieAlgebra.ad R L (t • y + n)) :=
  isNilpotent_ad_of_mem_span_singleton_sup_nilradical hy <| Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.smul_mem _ t (Submodule.mem_span_singleton_self y)))
    (Submodule.mem_sup_right ((LieSubmodule.mem_toSubmodule (nilradical R L)).mpr hn))

end TauCeti.LieAlgebra
