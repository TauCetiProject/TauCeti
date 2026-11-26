/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import TauCeti.Algebra.Homology.HomologicalComplex.ZeroDifferential
public import TauCeti.CategoryTheory.Exact.KernelCokernelPair
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import TauCeti.Algebra.Homology.HomologicalComplex.Basic
import TauCeti.CategoryTheory.Exact.HomologicalComplex

/-!
# The short exact sequence of cycles of a complex

Let `K` be a homological complex in a category with homology, for instance an abelian category,
and write `Zᵢ` for its cycles.  The cycles form a complex `K.cyclesComplex` with zero
differential, and so do the cokernels `Kᵢ / Zᵢ` of the inclusions of the cycles
(`K.cyclesCokernelComplex`).  Since the differential of `K` lands in the cycles, the inclusions
and the projections are chain maps, and they form a short complex of complexes

`0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0`

(`K.cyclesComplexShortComplex`), functorial in `K`.  It is a kernel–cokernel pair, since
degreewise the inclusion of the cycles is a kernel of the projection onto their cokernel, and
hence short exact.  In each degree where the inclusion of the cycles of `K` is a split
monomorphism, so is the first map of this sequence; in an abelian category the sequence is then
split in that degree, as happens for a complex of projective modules over a principal ideal
domain.  The inclusion of the cycles induces an epimorphism on homology, and the projection onto
`K / Z(K)` induces zero on homology, so in the abelian case the long exact homology sequence shows
that the connecting morphisms are monomorphisms.  In a degree where the differential out of `K`
vanishes, so does the homology of `K / Z(K)`.

Tensoring this sequence with a second complex compares the homology of a tensor product with
tensor products of homology, which is how it enters the Künneth formula.

## Main definitions and results

* `HomologicalComplex.cyclesComplex`, `HomologicalComplex.cyclesCokernelComplex` and
  `HomologicalComplex.cyclesComplexShortComplex`: the complexes and the short complex.
* `HomologicalComplex.cyclesComplexShortComplex_isKernelCokernelPair` and
  `HomologicalComplex.cyclesComplexShortComplex_shortExact`: it is a kernel–cokernel pair, and
  short exact.
* `HomologicalComplex.cyclesComplexShortComplexMap`: the morphism of short complexes induced by a
  chain map.
* `HomologicalComplex.epi_homologyMap_cyclesComplexShortComplex_f`: the inclusion of the cycles
  is an epimorphism on homology.
* `HomologicalComplex.homologyMap_cyclesComplexShortComplex_g`: the projection is zero on
  homology.
* `HomologicalComplex.isZero_homology_cyclesComplexShortComplex_X₃_of_d_eq_zero`: the homology of
  `K / Z(K)` vanishes in a degree where the differential out of `K` does; for a chain complex
  this holds in every degree `q` which is not of the form `q' + 1`, such as degree zero for chain
  complexes indexed by `ℕ`
  (`HomologicalComplex.isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne`).
* `HomologicalComplex.homologyPresentation`, `HomologicalComplex.homologyPresentation_shortExact`,
  `HomologicalComplex.homologyPresentationX₁Iso`, `HomologicalComplex.homologyPresentationX₂Iso`,
  and `HomologicalComplex.homologyPresentationMap`: in an abelian category, the short exact
  presentation `0 ⟶ H_i(K / Z(K)) ⟶ H_j(Z(K)) ⟶ H_j(K) ⟶ 0` for `c.Rel i j`, the canonical
  identifications of its first two terms with `K_i / Z_i(K)` and `Z_j(K)`, and its functoriality.

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

section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [CategoryWithHomology C] {ι : Type*}
  {c : ComplexShape ι} (K : HomologicalComplex C c)

/-- The complex of cycles of `K`, with zero differential. -/
abbrev cyclesComplex : HomologicalComplex C c :=
  graded c fun i ↦ K.cycles i

/-- The complex of cokernels of the inclusions of the cycles of `K`, with zero differential. -/
abbrev cyclesCokernelComplex : HomologicalComplex C c :=
  graded c fun i ↦ cokernel (K.iCycles i)

/-- The sequence of complexes `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` given by the inclusions of the cycles
and the projections onto their cokernels.  It is short exact
(`HomologicalComplex.cyclesComplexShortComplex_shortExact`). -/
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
@[simp]
lemma cyclesComplexShortComplex_f_f (i : ι) :
    K.cyclesComplexShortComplex.f.f i = eqToHom (by simp) ≫ K.iCycles i ≫ eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- In each degree, the second map of the cycle sequence is the projection onto the cokernel of
the inclusion of the cycles. -/
@[simp]
lemma cyclesComplexShortComplex_g_f (i : ι) :
    K.cyclesComplexShortComplex.g.f i =
      eqToHom (by simp) ≫ cokernel.π (K.iCycles i) ≫ eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- In each degree where the inclusion of the cycles of `K` is a split monomorphism, so is the
first map of the cycle sequence. -/
instance isSplitMono_cyclesComplexShortComplex_f_f (i : ι) [IsSplitMono (K.iCycles i)] :
    IsSplitMono (K.cyclesComplexShortComplex.f.f i) :=
  inferInstanceAs (IsSplitMono (K.iCycles i))

/-- In each degree, the first map of the cycle sequence is a monomorphism. -/
instance mono_cyclesComplexShortComplex_f_f (i : ι) : Mono (K.cyclesComplexShortComplex.f.f i) :=
  inferInstanceAs (Mono (K.iCycles i))

/-- The first map `Z(K) ⟶ K` of the cycle sequence is a monomorphism. -/
instance mono_cyclesComplexShortComplex_f : Mono K.cyclesComplexShortComplex.f :=
  mono_of_mono_f _ inferInstance

/-- In each degree, the second map of the cycle sequence is an epimorphism. -/
instance epi_cyclesComplexShortComplex_g_f (i : ι) : Epi (K.cyclesComplexShortComplex.g.f i) :=
  inferInstanceAs (Epi (cokernel.π (K.iCycles i)))

/-- The second map `K ⟶ K / Z(K)` of the cycle sequence is an epimorphism. -/
instance epi_cyclesComplexShortComplex_g : Epi K.cyclesComplexShortComplex.g :=
  epi_of_epi_f _ inferInstance

/-- The first map `Z(K) ⟶ K` of the cycle sequence is a kernel of the second, and the second
map `K ⟶ K / Z(K)` is a cokernel of the first. -/
lemma cyclesComplexShortComplex_isKernelCokernelPair :
    TauCeti.IsKernelCokernelPair K.cyclesComplexShortComplex :=
  -- In degree `i`, the cycles are a kernel of the differential, which factors through the
  -- projection onto their cokernel.
  .of_eval fun i ↦
    { nonempty_fIsKernel := ⟨isKernelOfComp _ _ (K.sc i).cyclesIsKernel
        (cokernel.condition (K.iCycles i))
        (cokernel.π_desc (K.iCycles i) (K.d i (c.next i)) (K.iCycles_d i _))⟩
      nonempty_gIsCokernel := ⟨cokernelIsCokernel (K.iCycles i)⟩ }

/-- The sequence of complexes `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` is short exact. -/
lemma cyclesComplexShortComplex_shortExact : K.cyclesComplexShortComplex.ShortExact := by
  -- The complex of the cokernels of the identities of the `Kᵢ` is a zero object.
  have : HasZeroObject (HomologicalComplex C c) := ⟨graded c fun i ↦ cokernel (𝟙 (K.X i)), by
    rw [IsZero.iff_id_eq_zero]
    exact hom_ext _ _ fun i ↦ (isZero_cokernel_of_epi (𝟙 (K.X i))).eq_of_src _ _⟩
  have := K.cyclesComplexShortComplex_isKernelCokernelPair.hasHomology
  exact K.cyclesComplexShortComplex_isKernelCokernelPair.shortExact

/-- The inclusion of the cycles induces an epimorphism on homology. -/
instance epi_homologyMap_cyclesComplexShortComplex_f (i : ι) :
    Epi (homologyMap K.cyclesComplexShortComplex.f i) := by
  -- Up to the identification of `Z(K)` with `graded c fun j ↦ K.cycles j`, the inclusion of the
  -- cycles is the morphism `K.fromGraded` given by their identities.
  have hf : K.cyclesComplexShortComplex.f = K.fromGraded fun j ↦ 𝟙 (K.cycles j) := by
    ext j
    simp [cyclesComplexShortComplex]
  rw [hf]
  exact K.epi_homologyMap_fromGraded _ i

/-- The projection of `K` onto `K / Z(K)` induces zero on cycles. -/
@[simp]
lemma cyclesMap_cyclesComplexShortComplex_g (i : ι) :
    cyclesMap K.cyclesComplexShortComplex.g i = 0 := by
  rw [← cancel_mono (K.cyclesComplexShortComplex.X₃.iCycles i), cyclesMap_i, zero_comp]
  exact cokernel.condition _

/-- The projection of `K` onto `K / Z(K)` induces zero on homology. -/
@[simp]
lemma homologyMap_cyclesComplexShortComplex_g (i : ι) :
    homologyMap K.cyclesComplexShortComplex.g i = 0 := by
  rw [← cancel_epi (K.cyclesComplexShortComplex.X₂.homologyπ i), homologyπ_naturality,
    cyclesMap_cyclesComplexShortComplex_g, zero_comp, comp_zero]

section Map

variable {K} {L : HomologicalComplex C c} (φ : K ⟶ L)

/-- A chain map `φ : K ⟶ L` induces a morphism from the cycle sequence
`0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` to `0 ⟶ Z(L) ⟶ L ⟶ L / Z(L) ⟶ 0`: it is `φ` on the middle terms,
and the maps induced by `φ` on cycles and on their cokernels on the outer terms. -/
def cyclesComplexShortComplexMap : K.cyclesComplexShortComplex ⟶ L.cyclesComplexShortComplex where
  τ₁ :=
    { f i := cyclesMap φ i
      comm' _ _ _ := comp_zero.trans zero_comp.symm }
  τ₂ := φ
  τ₃ :=
    { f i := cokernel.map (K.iCycles i) (L.iCycles i) (cyclesMap φ i) (φ.f i) (by simp)
      comm' _ _ _ := comp_zero.trans zero_comp.symm }
  comm₁₂ := by ext; simp [cyclesComplexShortComplex]
  comm₂₃ := by ext; simp [cyclesComplexShortComplex]

/-- In each degree, the morphism of cycle sequences induced by `φ` is the induced map on cycles
on the first terms. -/
@[simp]
lemma cyclesComplexShortComplexMap_τ₁_f (i : ι) :
    (cyclesComplexShortComplexMap φ).τ₁.f i =
      eqToHom (by simp) ≫ cyclesMap φ i ≫ eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- On the middle terms, the morphism of cycle sequences induced by `φ` is `φ`. -/
@[simp]
lemma cyclesComplexShortComplexMap_τ₂ :
    (cyclesComplexShortComplexMap φ).τ₂ =
      eqToHom K.cyclesComplexShortComplex_X₂ ≫ φ ≫ eqToHom L.cyclesComplexShortComplex_X₂.symm :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

/-- In each degree, the morphism of cycle sequences induced by `φ` is the induced map on the
cokernels of the inclusions of the cycles on the last terms. -/
@[simp]
lemma cyclesComplexShortComplexMap_τ₃_f (i : ι) :
    (cyclesComplexShortComplexMap φ).τ₃.f i = eqToHom (by simp) ≫
      cokernel.map (K.iCycles i) (L.iCycles i) (cyclesMap φ i) (φ.f i) (by simp) ≫
        eqToHom (by simp) :=
  (Category.comp_id _).symm.trans (Category.id_comp _).symm

variable (K) in
/-- The identity chain map induces the identity morphism of cycle sequences. -/
@[simp]
lemma cyclesComplexShortComplexMap_id :
    cyclesComplexShortComplexMap (𝟙 K) = 𝟙 K.cyclesComplexShortComplex := by
  ext <;> simp [cyclesComplexShortComplexMap, cyclesComplexShortComplex]

/-- The morphism of cycle sequences induced by a composite of chain maps is the composite of the
induced morphisms. -/
@[simp, reassoc]
lemma cyclesComplexShortComplexMap_comp {M : HomologicalComplex C c} (φ' : L ⟶ M) :
    cyclesComplexShortComplexMap (φ ≫ φ') =
      cyclesComplexShortComplexMap φ ≫ cyclesComplexShortComplexMap φ' := by
  ext i
  · exact cyclesMap_comp φ φ' i
  · rfl
  · exact coequalizer.hom_ext (by simp [cyclesComplexShortComplexMap, cyclesComplexShortComplex])

end Map

/-- If the differential of `K` out of degree `i` vanishes, all of `Kᵢ` consists of cycles, so the
third term `K / Z(K)` of the cycle sequence has zero homology in degree `i`. -/
lemma isZero_homology_cyclesComplexShortComplex_X₃_of_d_eq_zero (i : ι)
    (h : K.d i (c.next i) = 0) : IsZero (K.cyclesComplexShortComplex.X₃.homology i) := by
  have := K.isIso_iCycles i _ rfl h
  exact (K.cyclesCokernelComplex.sc i).isZero_homology_of_isZero_X₂
    (isZero_cokernel_of_epi (K.iCycles i))

/-- For a chain complex, all of `K_q` consists of cycles when `q` is not of the form `q' + 1`, for
instance for `q = 0` and chain complexes indexed by `ℕ`, so the third term `K / Z(K)` of the cycle
sequence has zero homology in degree `q`. -/
lemma isZero_homology_cyclesComplexShortComplex_X₃_of_forall_add_one_ne {α : Type*}
    [AddRightCancelSemigroup α] [One α] (K : ChainComplex C α) {q : α} (hq : ∀ q', q' + 1 ≠ q) :
    IsZero (K.cyclesComplexShortComplex.X₃.homology q) :=
  K.isZero_homology_cyclesComplexShortComplex_X₃_of_d_eq_zero q (K.shape _ _ (hq _))

end

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex C c)

/-- The connecting morphisms of `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` are monomorphisms. -/
instance mono_δ_cyclesComplexShortComplex {i j : ι} (hij : c.Rel i j) :
    Mono (K.cyclesComplexShortComplex_shortExact.δ i j hij) :=
  (K.cyclesComplexShortComplex_shortExact.homology_exact₃ i j hij).mono_g
    (K.homologyMap_cyclesComplexShortComplex_g i)

/-- For `c.Rel i j`, the short complex `H_i(K / Z(K)) ⟶ H_j(Z(K)) ⟶ H_j(K)` formed by the
connecting morphism of `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0` and the map induced by the inclusion of the
cycles. It is short exact (`HomologicalComplex.homologyPresentation_shortExact`), and since `Z(K)`
and `K / Z(K)` have zero differentials its first two terms are canonically isomorphic to
`K_i / Z_i(K)` (`HomologicalComplex.homologyPresentationX₁Iso`) and `Z_j(K)`
(`HomologicalComplex.homologyPresentationX₂Iso`). -/
abbrev homologyPresentation (i j : ι) (hij : c.Rel i j) : ShortComplex C :=
  ShortComplex.mk (K.cyclesComplexShortComplex_shortExact.δ i j hij)
    (homologyMap K.cyclesComplexShortComplex.f j ≫
      eqToHom (congrArg (·.homology j) K.cyclesComplexShortComplex_X₂)) (by simp)

/-- `H_i(K / Z(K)) ⟶ H_j(Z(K)) ⟶ H_j(K)` is short exact: it is a piece of the long exact homology
sequence of `0 ⟶ Z(K) ⟶ K ⟶ K / Z(K) ⟶ 0`, whose connecting morphisms are monomorphisms and whose
map `H(Z(K)) ⟶ H(K)` is an epimorphism. -/
lemma homologyPresentation_shortExact (i j : ι) (hij : c.Rel i j) :
    (K.homologyPresentation i j hij).ShortExact where
  exact := (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
    (S₂ := K.homologyPresentation i j hij)
    (S₁ := ShortComplex.mk (K.cyclesComplexShortComplex_shortExact.δ i j hij)
      (homologyMap K.cyclesComplexShortComplex.f j)
      (K.cyclesComplexShortComplex_shortExact.δ_comp i j hij))
    (Iso.refl _) (Iso.refl _) (eqToIso (congrArg (·.homology j) K.cyclesComplexShortComplex_X₂))
    (by simp) (by simp))).1
    (K.cyclesComplexShortComplex_shortExact.homology_exact₁ i j hij)
  mono_f := K.mono_δ_cyclesComplexShortComplex hij
  epi_g := epi_comp _ _

/-- The first term `H_i(K / Z(K))` of `HomologicalComplex.homologyPresentation` is canonically
isomorphic to `K_i / Z_i(K)` because `K / Z(K)` has zero differential. -/
def homologyPresentationX₁Iso (i j : ι) (hij : c.Rel i j) :
    (K.homologyPresentation i j hij).X₁ ≅ cokernel (K.iCycles i) :=
  (K.cyclesComplexShortComplex.X₃.XIsoHomologyOfDEqZero i (by simp) (by simp)).symm ≪≫
    eqToIso (by simp)

/-- The forward map of `HomologicalComplex.homologyPresentationX₁Iso`. -/
@[simp]
lemma homologyPresentationX₁Iso_hom (i j : ι) (hij : c.Rel i j) :
    (K.homologyPresentationX₁Iso i j hij).hom =
      (K.cyclesComplexShortComplex.X₃.XIsoHomologyOfDEqZero i (by simp) (by simp)).inv ≫
        eqToHom (by simp) :=
  (rfl)

/-- The inverse map of `HomologicalComplex.homologyPresentationX₁Iso`. -/
@[simp]
lemma homologyPresentationX₁Iso_inv (i j : ι) (hij : c.Rel i j) :
    (K.homologyPresentationX₁Iso i j hij).inv =
      eqToHom (by simp) ≫
        (K.cyclesComplexShortComplex.X₃.XIsoHomologyOfDEqZero i (by simp) (by simp)).hom :=
  (rfl)

/-- The middle term `H_j(Z(K))` of `HomologicalComplex.homologyPresentation` is canonically
isomorphic to `Z_j(K)` because `Z(K)` has zero differential. -/
def homologyPresentationX₂Iso (i j : ι) (hij : c.Rel i j) :
    (K.homologyPresentation i j hij).X₂ ≅ K.cycles j :=
  (K.cyclesComplexShortComplex.X₁.XIsoHomologyOfDEqZero j (by simp) (by simp)).symm ≪≫
    eqToIso (by simp)

/-- The forward map of `HomologicalComplex.homologyPresentationX₂Iso`. -/
@[simp]
lemma homologyPresentationX₂Iso_hom (i j : ι) (hij : c.Rel i j) :
    (K.homologyPresentationX₂Iso i j hij).hom =
      (K.cyclesComplexShortComplex.X₁.XIsoHomologyOfDEqZero j (by simp) (by simp)).inv ≫
        eqToHom (by simp) :=
  (rfl)

/-- The inverse map of `HomologicalComplex.homologyPresentationX₂Iso`. -/
@[simp]
lemma homologyPresentationX₂Iso_inv (i j : ι) (hij : c.Rel i j) :
    (K.homologyPresentationX₂Iso i j hij).inv =
      eqToHom (by simp) ≫
        (K.cyclesComplexShortComplex.X₁.XIsoHomologyOfDEqZero j (by simp) (by simp)).hom :=
  (rfl)

/-- The first term `H_i(K / Z(K))` of `HomologicalComplex.homologyPresentation` is projective when
`K_i / Z_i(K)` is projective. -/
instance projective_homologyPresentation_X₁ (i j : ι) (hij : c.Rel i j)
    [Projective (cokernel (K.iCycles i))] : Projective (K.homologyPresentation i j hij).X₁ :=
  Projective.of_iso (K.homologyPresentationX₁Iso i j hij).symm inferInstance

/-- The middle term `H_j(Z(K))` of `HomologicalComplex.homologyPresentation` is projective when
`Z_j(K)` is projective. -/
instance projective_homologyPresentation_X₂ (i j : ι) (hij : c.Rel i j)
    [Projective (K.cycles j)] : Projective (K.homologyPresentation i j hij).X₂ :=
  Projective.of_iso (K.homologyPresentationX₂Iso i j hij).symm inferInstance

variable {K} {L : HomologicalComplex C c}

/-- The morphism of presentations `K.homologyPresentation i j hij ⟶ L.homologyPresentation i j hij`
induced by a chain map `ψ : K ⟶ L`. -/
def homologyPresentationMap (ψ : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    K.homologyPresentation i j hij ⟶ L.homologyPresentation i j hij where
  τ₁ := homologyMap (cyclesComplexShortComplexMap ψ).τ₃ i
  τ₂ := homologyMap (cyclesComplexShortComplexMap ψ).τ₁ j
  τ₃ := homologyMap ψ j
  comm₁₂ := (HomologySequence.δ_naturality (cyclesComplexShortComplexMap ψ)
    K.cyclesComplexShortComplex_shortExact L.cyclesComplexShortComplex_shortExact i j hij).symm
  comm₂₃ := by
    dsimp only [homologyPresentation]
    rw [← homologyMap_comp_assoc, (cyclesComplexShortComplexMap ψ).comm₁₂, homologyMap_comp_assoc,
      homologyMap_comp_eqToHom ψ K.cyclesComplexShortComplex_X₂ L.cyclesComplexShortComplex_X₂ _
        (cyclesComplexShortComplexMap_τ₂ ψ), Category.assoc]

/-- The first component of `HomologicalComplex.homologyPresentationMap`. -/
@[simp]
lemma homologyPresentationMap_τ₁ (ψ : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (homologyPresentationMap ψ i j hij).τ₁ = homologyMap (cyclesComplexShortComplexMap ψ).τ₃ i :=
  (rfl)

/-- The second component of `HomologicalComplex.homologyPresentationMap`. -/
@[simp]
lemma homologyPresentationMap_τ₂ (ψ : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (homologyPresentationMap ψ i j hij).τ₂ = homologyMap (cyclesComplexShortComplexMap ψ).τ₁ j :=
  (rfl)

/-- The third component of `HomologicalComplex.homologyPresentationMap`. -/
@[simp]
lemma homologyPresentationMap_τ₃ (ψ : K ⟶ L) (i j : ι) (hij : c.Rel i j) :
    (homologyPresentationMap ψ i j hij).τ₃ = homologyMap ψ j :=
  (rfl)

end Abelian

end HomologicalComplex
