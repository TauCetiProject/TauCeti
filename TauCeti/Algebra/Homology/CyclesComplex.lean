/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic

/-!
# The short exact sequence of cycles of a complex

Let `K` be a homological complex in an abelian category, and write `Zᵢ` for its cycles.  The
cycles form a complex `K.cyclesComplex` with zero differential, and so do the cokernels
`Kᵢ / Zᵢ` of the inclusions of the cycles (`K.cyclesCokernelComplex`).  Since the differential of
`K` lands in the cycles, the inclusions and the projections are chain maps, and they form a short
exact sequence of complexes

`0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0`

(`K.cyclesComplexShortComplex`).  It is split in each degree when the cycles of `K` split off its
terms, as happens for a complex of projective modules over a principal ideal domain.  The map it
induces on homology from `K` to `K / Z(K)` vanishes, so in its long exact homology sequence the
map induced by the inclusion of the cycles is an epimorphism and the connecting morphisms are
monomorphisms.  A chain map `K ⟶ L` induces a morphism from the sequence of `K` to that of `L`
(`HomologicalComplex.cyclesComplexShortComplexMap`).

Tensoring this sequence with a second complex compares the homology of a tensor product with
tensor products of homology, which is how it enters the Künneth formula.

## Main definitions and results

* `HomologicalComplex.cyclesComplex`, `HomologicalComplex.cyclesCokernelComplex` and
  `HomologicalComplex.cyclesComplexShortComplex`: the complexes and the short complex.
* `HomologicalComplex.cyclesComplexShortComplex_shortExact`: it is short exact.
* `HomologicalComplex.cyclesComplexShortComplexMap`: the morphism of cycle sequences induced by a
  chain map.
* `HomologicalComplex.homologyMap_cyclesComplexShortComplex_g`: the projection is zero on
  homology.
* `HomologicalComplex.isZero_homology_cyclesComplexShortComplex_X₃_zero`: for a chain complex
  indexed by `ℕ`, the homology of `K / Z(K)` vanishes in degree zero.

## Implementation notes

The two complexes are reducible, so that their terms are seen to be the cycles and their cokernels
when typing the components `K.iCycles i` and `cokernel.π (K.iCycles i)` of the chain maps, here
and in the files using them.  The body of `HomologicalComplex.cyclesComplexShortComplex` is not
exposed; it is characterised by the lemmas `cyclesComplexShortComplex_X₁` and its siblings, which
identify its terms, differentials and components.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, proof of Theorem 3.6.3.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

/-- The complex of cycles of `K`, with zero differential. -/
@[simps]
abbrev cyclesComplex : HomologicalComplex C c where
  X i := K.cycles i
  d _ _ := 0

/-- The complex of cokernels of the inclusions of the cycles of `K`, with zero differential. -/
@[simps]
abbrev cyclesCokernelComplex : HomologicalComplex C c where
  X i := cokernel (K.iCycles i)
  d _ _ := 0

/-- The short exact sequence of complexes `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` given by the inclusions
of the cycles and the projections onto their cokernels. -/
def cyclesComplexShortComplex : ShortComplex (HomologicalComplex C c) where
  X₁ := K.cyclesComplex
  X₂ := K
  X₃ := K.cyclesCokernelComplex
  f :=
    { f i := K.iCycles i
      comm' i j _ := by simp }
  g :=
    { f i := cokernel.π (K.iCycles i)
      comm' i j _ := by simp [← K.toCycles_i_assoc] }
  zero := by ext; simp

/-- The first term of the cycle sequence of `K` is the complex of cycles `Z(K)`. -/
@[simp] lemma cyclesComplexShortComplex_X₁ : K.cyclesComplexShortComplex.X₁ = K.cyclesComplex :=
  (rfl)

/-- The middle term of the cycle sequence of `K` is `K` itself. -/
@[simp] lemma cyclesComplexShortComplex_X₂ : K.cyclesComplexShortComplex.X₂ = K := (rfl)

/-- The last term of the cycle sequence of `K` is the complex `K / Z(K)`. -/
@[simp] lemma cyclesComplexShortComplex_X₃ :
    K.cyclesComplexShortComplex.X₃ = K.cyclesCokernelComplex :=
  (rfl)

/-- The first term `Z(K)` of the cycle sequence has zero differential. -/
@[simp] lemma cyclesComplexShortComplex_X₁_d (i j : ι) : K.cyclesComplexShortComplex.X₁.d i j = 0 :=
  (rfl)

/-- The last term `K / Z(K)` of the cycle sequence has zero differential. -/
@[simp] lemma cyclesComplexShortComplex_X₃_d (i j : ι) : K.cyclesComplexShortComplex.X₃.d i j = 0 :=
  (rfl)

/-- In each degree, the first map of the cycle sequence is the inclusion of the cycles. -/
lemma cyclesComplexShortComplex_f_f (i : ι) :
    K.cyclesComplexShortComplex.f.f i = eqToHom (by simp) ≫ K.iCycles i ≫ eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- In each degree, the second map of the cycle sequence is the projection onto the cokernel of
the inclusion of the cycles. -/
lemma cyclesComplexShortComplex_g_f (i : ι) :
    K.cyclesComplexShortComplex.g.f i =
      eqToHom (by simp) ≫ cokernel.π (K.iCycles i) ≫ eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- The sequence of complexes `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` is short exact. -/
lemma cyclesComplexShortComplex_shortExact : K.cyclesComplexShortComplex.ShortExact :=
  shortExact_of_degreewise_shortExact _ fun i ↦
    ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (K.iCycles i))) (inferInstanceAs (Mono (K.iCycles i)))
      (inferInstanceAs (Epi (cokernel.π (K.iCycles i))))

instance [∀ i, IsSplitMono (K.iCycles i)] (i : ι) :
    IsSplitMono (K.cyclesComplexShortComplex.f.f i) :=
  inferInstanceAs (IsSplitMono (K.iCycles i))

/-- The projection of `K` onto `K / Z(K)` induces zero on homology. -/
@[simp]
lemma homologyMap_cyclesComplexShortComplex_g (i : ι) :
    homologyMap K.cyclesComplexShortComplex.g i = 0 := by
  have : cyclesMap K.cyclesComplexShortComplex.g i = 0 := by
    rw [← cancel_mono (K.cyclesComplexShortComplex.X₃.iCycles i), cyclesMap_i, zero_comp]
    exact cokernel.condition _
  rw [← cancel_epi (K.cyclesComplexShortComplex.X₂.homologyπ i), homologyπ_naturality, this,
    zero_comp, comp_zero]

/-- The inclusion of the cycles induces an epimorphism on homology. -/
instance epi_homologyMap_cyclesComplexShortComplex_f (i : ι) :
    Epi (homologyMap K.cyclesComplexShortComplex.f i) :=
  (K.cyclesComplexShortComplex_shortExact.homology_exact₂ i).epi_f
    (K.homologyMap_cyclesComplexShortComplex_g i)

/-- The connecting morphisms of `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` are monomorphisms. -/
instance mono_δ_cyclesComplexShortComplex {i j : ι} (hij : c.Rel i j) :
    Mono (K.cyclesComplexShortComplex_shortExact.δ i j hij) :=
  (K.cyclesComplexShortComplex_shortExact.homology_exact₃ i j hij).mono_g
    (K.homologyMap_cyclesComplexShortComplex_g i)

section Map

variable {K} {L : HomologicalComplex C c} (φ : K ⟶ L)

/-! The `eqToHom`s in the component lemmas below are identities: the terms of the cycle sequence
are the complexes named in `cyclesComplexShortComplex_X₁` and its siblings by `rfl`, so each lemma
holds by the unit laws.  They are stated with `eqToHom`s because the body of
`cyclesComplexShortComplex` is not exposed outside this file. -/

/-- A chain map `φ : K ⟶ L` induces a morphism from the cycle sequence
`0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` of `K` to that of `L`: the map `cyclesMap φ` on cycles, `φ` itself,
and the induced map on the cokernels of the inclusions of the cycles. -/
def cyclesComplexShortComplexMap : K.cyclesComplexShortComplex ⟶ L.cyclesComplexShortComplex where
  τ₁ :=
    { f i := cyclesMap φ i
      comm' i j _ := comp_zero.trans zero_comp.symm }
  τ₂ := φ
  τ₃ :=
    { f i := cokernel.map (K.iCycles i) (L.iCycles i) (cyclesMap φ i) (φ.f i) (by simp)
      comm' i j _ := comp_zero.trans zero_comp.symm }
  comm₁₂ := by ext; simp [cyclesComplexShortComplex]
  comm₂₃ := by ext; simp [cyclesComplexShortComplex]

/-- The middle component of the morphism of cycle sequences induced by `φ` is `φ`. -/
lemma cyclesComplexShortComplexMap_τ₂ :
    (cyclesComplexShortComplexMap φ).τ₂ = eqToHom (by simp) ≫ φ ≫ eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- In each degree, the first component of the morphism of cycle sequences induced by `φ` is the
map `cyclesMap φ` of cycles. -/
lemma cyclesComplexShortComplexMap_τ₁_f (i : ι) :
    (cyclesComplexShortComplexMap φ).τ₁.f i =
      eqToHom (by simp) ≫ cyclesMap φ i ≫ eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- In each degree, the last component of the morphism of cycle sequences induced by `φ` is the
map of cokernels of the inclusions of the cycles induced by `φ`. -/
lemma cyclesComplexShortComplexMap_τ₃_f (i : ι) :
    (cyclesComplexShortComplexMap φ).τ₃.f i = eqToHom (by simp) ≫
      cokernel.map (K.iCycles i) (L.iCycles i) (cyclesMap φ i) (φ.f i) (by simp) ≫
        eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

end Map

/-- For a chain complex indexed by `ℕ`, all of `K₀` consists of cycles, so the third term
`K / Z(K)` of the cycle sequence has zero homology in degree zero. -/
lemma isZero_homology_cyclesComplexShortComplex_X₃_zero (K : ChainComplex C ℕ) :
    IsZero (K.cyclesComplexShortComplex.X₃.homology 0) := by
  have := K.isIso_iCycles 0 0 (by simp) (K.shape _ _ (by simp))
  exact (K.cyclesCokernelComplex.sc 0).isZero_homology_of_isZero_X₂
    (isZero_cokernel_of_epi (K.iCycles 0))

end HomologicalComplex
