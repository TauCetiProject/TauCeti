/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Pullback
public import TauCeti.RingTheory.TwoSidedIdeal.Quotient

/-!
# The double of a ring along a two-sided ideal

For a two-sided ideal `I` of an associative unital ring `R`, the *double* `R ⊕ I` is the ring of
pairs `(r, x)` with `x ∈ I` and product `(r, x) (s, y) = (r s, r y + x s + x y)`. It comes with two
ring homomorphisms to `R`, the projection `pr (r, x) = r` and the addition map
`add (r, x) = r + x`, and `pr` is split by the diagonal `r ↦ (r, 0)`.

The map `(r, x) ↦ (r, r + x)` identifies `R ⊕ I` with the fibre product `R ×_{R/I} R` of two copies
of the quotient map `R → R ⧸ I`: the subring of `R × R` of pairs whose coordinates agree modulo
`I`. We take this fibre product as the definition, `TwoSidedIdeal.double`. Under the
identification `pr` and `add` become the two coordinate projections `TwoSidedIdeal.doubleFst` and
`TwoSidedIdeal.doubleSnd`, the diagonal section becomes `r ↦ (r, r)`, the elements `(0, v)` of the
kernel `0 ⊕ I` of `pr` stay `(0, v)`, and the elements `(v, -v)` of the kernel of `add` become
`(v, 0)`.

The double is the ring through which Keune and Loday define the relative Steinberg group and the
relative `K₂` of a pair `(R, I)`.

## Main definitions

* `TwoSidedIdeal.double`: the double of `R` along `I`, as a subring of `R × R`.
* `TwoSidedIdeal.doubleFst`, `TwoSidedIdeal.doubleSnd`: the projection and addition maps to `R`.
* `TwoSidedIdeal.doubleDiag`: the diagonal section `r ↦ (r, r)` of both maps.
* `TwoSidedIdeal.doubleInl`, `TwoSidedIdeal.doubleInr`: the elements `(v, 0)` and `(0, v)` for
  `v ∈ I`, which span the kernels of `doubleSnd` and `doubleFst`.
* `TwoSidedIdeal.doubleMap`: the homomorphism of doubles induced by a morphism of pairs.

## References

* F. Keune, *The relativization of K₂*, J. Algebra 54 (1978), 159–177.
* J.-L. Loday, *Cohomologie et groupe de Steinberg relatifs*, J. Algebra 54 (1978), 178–202.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Definition 5.7.
-/

public section

namespace TwoSidedIdeal

section Comap

variable {R S T : Type*} [NonAssocRing R] [NonAssocRing S] [NonAssocRing T]
  {I : TwoSidedIdeal R} {J : TwoSidedIdeal S} {K : TwoSidedIdeal T}

variable (I) in
/-- The identity is a morphism of pairs `(R, I) → (R, I)`. -/
theorem le_comap_id : I ≤ comap (RingHom.id R) I :=
  fun _ hx ↦ (mem_comap _).2 hx

/-- A composite of morphisms of pairs `(R, I) → (S, J) → (T, K)` is a morphism of pairs. -/
theorem le_comap_comp {f : R →+* S} {g : S →+* T} (hf : I ≤ comap f J) (hg : J ≤ comap g K) :
    I ≤ comap (g.comp f) K :=
  fun _ hx ↦ (mem_comap _).2 ((mem_comap g).1 (hg ((mem_comap f).1 (hf hx))))

end Comap

variable {R S T : Type*} [Ring R] [Ring S] [Ring T] (I : TwoSidedIdeal R) (J : TwoSidedIdeal S)
  (K : TwoSidedIdeal T)

/-- The **double** `R ⊕ I` of a ring `R` along a two-sided ideal `I`, realized as the fibre product
`R ×_{R/I} R` of two copies of the quotient map: the subring of pairs in `R × R` whose coordinates
agree modulo `I`. The pair `(r, x)` of `R ⊕ I` corresponds to `(r, r + x)`. -/
def double : Subring (R × R) :=
  RingHom.pullback (Quotient.mkRingHom I) (Quotient.mkRingHom I)

variable {I} in
/-- A pair lies in the double exactly when its coordinates agree modulo `I`. -/
@[simp]
theorem mem_double_iff {p : R × R} : p ∈ I.double ↔ p.1 - p.2 ∈ I := by
  simp only [double, RingHom.mem_eqLocus, RingHom.coe_comp, Function.comp_apply, RingHom.coe_fst,
    RingHom.coe_snd, Quotient.coe_mkRingHom, Quotient.eq]

/-- The projection `pr : R ⊕ I →+* R`, `(r, x) ↦ r`, which is the first coordinate of the fibre
product. -/
def doubleFst : I.double →+* R :=
  RingHom.pullbackFst (Quotient.mkRingHom I) (Quotient.mkRingHom I)

/-- The addition map `add : R ⊕ I →+* R`, `(r, x) ↦ r + x`, which is the second coordinate of the
fibre product. -/
def doubleSnd : I.double →+* R :=
  RingHom.pullbackSnd (Quotient.mkRingHom I) (Quotient.mkRingHom I)

@[simp]
theorem doubleFst_apply (p : I.double) : I.doubleFst p = (p : R × R).1 :=
  (rfl)

@[simp]
theorem doubleSnd_apply (p : I.double) : I.doubleSnd p = (p : R × R).2 :=
  (rfl)

/-- The projection and the addition map are the two coordinates of the inclusion `R ⊕ I → R × R`.
-/
theorem doubleFst_prod_doubleSnd : I.doubleFst.prod I.doubleSnd = I.double.subtype :=
  RingHom.ext fun _ ↦ (rfl)

/-- The projection and the addition map are jointly injective. -/
theorem doubleFst_prod_doubleSnd_injective :
    Function.Injective (I.doubleFst.prod I.doubleSnd) := by
  rw [doubleFst_prod_doubleSnd]
  exact Subtype.val_injective

/-- The diagonal `R →+* R ⊕ I`, `r ↦ (r, 0)`, which is `r ↦ (r, r)` in the fibre product. It is a
section of both the projection and the addition map. -/
def doubleDiag : R →+* I.double :=
  (RingHom.prod (RingHom.id R) (RingHom.id R)).codRestrict I.double fun r ↦ by simp

@[simp]
theorem coe_doubleDiag_apply (r : R) : (I.doubleDiag r : R × R) = (r, r) :=
  (rfl)

@[simp]
theorem doubleFst_comp_doubleDiag : I.doubleFst.comp I.doubleDiag = RingHom.id R :=
  (rfl)

@[simp]
theorem doubleSnd_comp_doubleDiag : I.doubleSnd.comp I.doubleDiag = RingHom.id R :=
  (rfl)

theorem doubleFst_surjective : Function.Surjective I.doubleFst :=
  fun r ↦ ⟨I.doubleDiag r, rfl⟩

theorem doubleSnd_surjective : Function.Surjective I.doubleSnd :=
  fun r ↦ ⟨I.doubleDiag r, rfl⟩

variable {I}

/-- The element `(v, -v)` of `R ⊕ I`, for `v ∈ I`, which is `(v, 0)` in the fibre product. These
elements form the kernel of the addition map. -/
def doubleInl {v : R} (hv : v ∈ I) : I.double :=
  ⟨(v, 0), by simpa using hv⟩

/-- The element `(0, v)` of `R ⊕ I`, for `v ∈ I`. These elements form the kernel of the
projection. -/
def doubleInr {v : R} (hv : v ∈ I) : I.double :=
  ⟨(0, v), by simpa using hv⟩

@[simp]
theorem coe_doubleInl {v : R} (hv : v ∈ I) : (doubleInl hv : R × R) = (v, 0) :=
  (rfl)

@[simp]
theorem coe_doubleInr {v : R} (hv : v ∈ I) : (doubleInr hv : R × R) = (0, v) :=
  (rfl)

theorem doubleFst_doubleInl {v : R} (hv : v ∈ I) : I.doubleFst (doubleInl hv) = v :=
  (rfl)

theorem doubleSnd_doubleInl {v : R} (hv : v ∈ I) : I.doubleSnd (doubleInl hv) = 0 :=
  (rfl)

theorem doubleFst_doubleInr {v : R} (hv : v ∈ I) : I.doubleFst (doubleInr hv) = 0 :=
  (rfl)

theorem doubleSnd_doubleInr {v : R} (hv : v ∈ I) : I.doubleSnd (doubleInr hv) = v :=
  (rfl)

/-- The second minus the first coordinate of an element of the double lies in `I`. -/
theorem doubleSnd_sub_doubleFst_mem (p : I.double) : I.doubleSnd p - I.doubleFst p ∈ I := by
  rw [← neg_sub, neg_mem_iff]
  exact mem_double_iff.1 p.property

/-- Every element of `R ⊕ I` is the sum of a diagonal element and an element `(0, v)` of the
kernel of the projection: `(r, x) = (r, 0) + (0, x)`. -/
theorem doubleDiag_add_doubleInr (p : I.double) :
    I.doubleDiag (I.doubleFst p) + doubleInr (doubleSnd_sub_doubleFst_mem p) = p :=
  Subtype.ext <| Prod.ext (add_zero _) (add_sub_cancel _ _)

/-- An element of the double is in the kernel of the projection exactly when it is `(0, v)` for
some `v ∈ I`. -/
theorem doubleFst_eq_zero_iff {p : I.double} :
    I.doubleFst p = 0 ↔ ∃ (v : R) (hv : v ∈ I), doubleInr hv = p := by
  refine ⟨fun hp ↦ ⟨I.doubleSnd p, ?_, Subtype.ext (Prod.ext hp.symm rfl)⟩, ?_⟩
  · simpa [hp] using doubleSnd_sub_doubleFst_mem p
  · rintro ⟨v, hv, rfl⟩
    exact doubleFst_doubleInr hv

/-- The projection `R ⊕ I →+* R` is injective exactly when `I` is zero. -/
theorem doubleFst_injective_iff : Function.Injective I.doubleFst ↔ I = ⊥ := by
  refine ⟨fun h ↦ eq_bot_iff.2 fun v hv ↦ (mem_bot R).2 ?_, fun h p q hpq ↦ ?_⟩
  · simpa using congrArg (fun p : I.double ↦ (p : R × R).2)
      (@h (doubleInr hv) 0 ((doubleFst_doubleInr hv).trans (map_zero _).symm))
  · subst h
    have hp := mem_double_iff.1 p.property
    have hq := mem_double_iff.1 q.property
    rw [mem_bot, sub_eq_zero] at hp hq
    exact Subtype.ext <| Prod.ext hpq (hp.symm.trans (hpq.trans hq))

variable {J K}

/-- The homomorphism of doubles `R ⊕ I →+* S ⊕ J` induced by a ring homomorphism `f : R →+* S`
carrying `I` into `J`, applying `f` to both coordinates. -/
def doubleMap (f : R →+* S) (h : I ≤ comap f J) : I.double →+* J.double :=
  (f.prodMap f).restrict I.double J.double fun p hp ↦ by
    simpa [← map_sub] using (mem_comap f).1 (h (mem_double_iff.1 hp))

@[simp]
theorem coe_doubleMap_apply (f : R →+* S) (h : I ≤ comap f J) (p : I.double) :
    (doubleMap f h p : S × S) = (f (p : R × R).1, f (p : R × R).2) :=
  (rfl)

@[simp]
theorem doubleFst_comp_doubleMap (f : R →+* S) (h : I ≤ comap f J) :
    J.doubleFst.comp (doubleMap f h) = f.comp I.doubleFst :=
  (rfl)

@[simp]
theorem doubleSnd_comp_doubleMap (f : R →+* S) (h : I ≤ comap f J) :
    J.doubleSnd.comp (doubleMap f h) = f.comp I.doubleSnd :=
  (rfl)

@[simp]
theorem doubleMap_doubleInl (f : R →+* S) (h : I ≤ comap f J) {v : R} (hv : v ∈ I) :
    doubleMap f h (doubleInl hv) = doubleInl ((mem_comap f).1 (h hv)) :=
  Subtype.ext <| Prod.ext (rfl) (map_zero f)

@[simp]
theorem doubleMap_doubleInr (f : R →+* S) (h : I ≤ comap f J) {v : R} (hv : v ∈ I) :
    doubleMap f h (doubleInr hv) = doubleInr ((mem_comap f).1 (h hv)) :=
  Subtype.ext <| Prod.ext (map_zero f) (rfl)

variable (I) in
@[simp]
theorem doubleMap_id :
    doubleMap (RingHom.id R) (le_comap_id I) = RingHom.id I.double :=
  (rfl)

theorem doubleMap_comp (f : R →+* S) (g : S →+* T) (hf : I ≤ comap f J) (hg : J ≤ comap g K) :
    doubleMap (g.comp f) (le_comap_comp hf hg) = (doubleMap g hg).comp (doubleMap f hf) :=
  (rfl)

end TwoSidedIdeal
