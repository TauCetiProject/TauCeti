/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import TauCeti.Algebra.Homology.Embedding.CochainComplex
public import TauCeti.CategoryTheory.GrothendieckGroup.Abelian

/-!
# The Euler characteristic of a bounded complex in abelian and exact `K₀`

For a cochain complex `K` over an abelian category `A` and an invariant `v` additive on short
exact sequences, the alternating sum

```text
∑ n ∈ s, (-1)ⁿ v(Kⁿ)
```

over a finite set `s` of degrees is the **Euler characteristic** of `K` relative to `v`. This file
proves the **Euler–Poincaré theorem**: as soon as `K` is bounded and `s` contains every degree
where `K` lives, this alternating sum equals the alternating sum formed from the cohomology
objects of `K`. The argument is carried out for an arbitrary additive invariant, so it needs no
smallness hypothesis on `A`; specializing it to the tautological invariant `X ↦ [X]` gives the
statement in `TauCeti.AbelianK0 A`, which is the form the rest of the theory consumes.

The finiteness is carried by data, not inferred: the summation range is an explicit `Finset ℤ`.
Nothing here is a `finsum`, so every value is a truncation to an explicitly given finite range of
degrees, and what boundedness buys is that all large enough ranges give the same answer.

Which boundedness is needed depends on what is being summed. The alternating class of the *terms*,
and with it Euler–Poincaré, needs the terms to vanish outside a finite range, which is Mathlib's
`CochainComplex.IsStrictlyGE`/`CochainComplex.IsStrictlyLE`. The alternating class of the
*cohomology* needs only the cohomology to vanish there, which is `IsGE`/`IsLE`; so a complex whose
terms are nonzero in every degree, such as an unbounded resolution, still has a range-independent
`homologyEulerChar`, while having no canonical `eulerChar`. A complex outside both regimes is
assigned no canonical value rather than a junk one. The comparison with the totalized
`HomologicalComplex.eulerChar` of Mathlib is left to the finite-dimensionality layer that gives it
a `ℤ`-valued additive invariant.

The same comparison holds in the exact `K₀` of an extension-closed full subcategory `P` of `A`,
with its induced exact structure, under explicit closure hypotheses on the complex: the boundaries
`im dⁿ` and the cohomology objects of `K` must lie in `P`. The cocycles are then extensions of the
cohomology by the boundaries, and the terms extensions of the boundaries by the cocycles, so both
lie in `P` too, and every short exact sequence used by the argument is a conflation of the
subcategory. The statement is at the level of the complex: no derived category of the
subcategory is formed. Both theorems run on one telescoping engine,
`HomologicalComplex.sum_negOnePow_X_eq_sum_negOnePow_homology`, which needs of a function on
objects only that it vanishes on zero objects and satisfies the degreewise homology relation.

## Main definitions

* `TauCeti.AbelianK0.eulerChar`: the alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` of the terms of a
  cochain complex over a finite set of degrees.
* `TauCeti.AbelianK0.homologyEulerChar`: the same alternating class formed from the cohomology
  objects.

## Main results

* `HomologicalComplex.sum_negOnePow_X_eq_sum_negOnePow_homology`: the telescoping argument for
  any function on objects satisfying the degreewise homology relation.
* `TauCeti.AbelianK0.AdditiveInvariant.obj_kernel_add_obj_kernel`: for a short complex `S` in an
  abelian category, `v(ker S.g) + v(ker S.f) = v(S.homology) + v(S.X₁)`. This is the single
  relation from which the telescoping argument runs.
* `TauCeti.AbelianK0.AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology`:
  **Euler–Poincaré**. A bounded complex has the same Euler characteristic computed from its terms
  and from its cohomology, for every invariant additive on short exact sequences.
* `TauCeti.AbelianK0.of_kernel_add_of_kernel` and
  `TauCeti.AbelianK0.eulerChar_eq_homologyEulerChar`: the two statements above in abelian `K₀`.
* `TauCeti.AbelianK0.homologyEulerChar_eq_homologyEulerChar`: the alternating class of the
  cohomology does not depend on the summation range as soon as the cohomology is bounded; the
  terms of the complex need not be.
* `TauCeti.AbelianK0.eulerChar_eq_of_quasiIso`: the Euler characteristic of a bounded complex
  depends only on its image in the derived category.
* `TauCeti.ExactStructure.IsExtensionClosed.prop_kernel_d` and
  `TauCeti.ExactStructure.IsExtensionClosed.prop_X`: if the boundaries and the cohomology of a
  complex lie in an extension-closed property, then so do its cocycles and its terms.
* `TauCeti.ExactK0.AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology` and
  `TauCeti.ExactK0.sum_negOnePow_of_X_eq_sum_negOnePow_of_homology`: **Euler–Poincaré in an
  extension-closed subcategory**, for an additive invariant of the subcategory and in its exact
  `K₀`.

## References

* Charles A. Weibel, *An Introduction to Homological Algebra*, Sections 1.3 and 1.6, for the
  cycles/boundaries bookkeeping behind the Euler–Poincaré formula.
* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Proposition 6.6, for the `K₀`-valued form of the alternating sum used here, and
  Proposition 7.5, for the Euler characteristic in an exact subcategory of an abelian category
  and its closure hypotheses.
-/

public section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A]

private theorem isZero_kernel_of_isZero {X Y : A} (f : X ⟶ Y) (hX : IsZero X) :
    IsZero (kernel f) :=
  IsZero.of_iso hX (kernelIsoOfEq (hX.eq_of_src f 0) ≪≫ kernelZeroIsoSource)

namespace HomologicalComplex

variable {G : Type*} [AddCommGroup G] (K : CochainComplex A ℤ) {w : A → G}

/-- The running form of the Euler–Poincaré computation: over the degrees `a` to `b` of a complex
that is strictly bounded below by `a`, the two alternating sums differ by the single correction
term supplied by the cocycles in degree `b + 1`. -/
private theorem sum_negOnePow_Icc_aux (hzero : ∀ X : A, IsZero X → w X = 0)
    (hrel : ∀ i j k : ℤ, i + 1 = j → j + 1 = k →
      w (kernel (K.d j k)) + w (kernel (K.d i j)) = w (K.homology j) + w (K.X i))
    (a : ℤ) [K.IsStrictlyGE a] (b : ℤ) (hb : a ≤ b) :
    ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • w (K.X n)
      = ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • w (K.homology n)
        + (((b + 1).negOnePow : ℤ)) •
          (w (K.homology (b + 1)) - w (kernel (K.d (b + 1) (b + 1 + 1)))) := by
  induction b, hb using Int.leInduction with
  | base =>
      -- below `a` the complex vanishes, so the cocycles in degree `a` are the cohomology
      have hlow := hrel (a - 1) a (a + 1) (by omega) rfl
      have hX₀ : IsZero (K.X (a - 1)) := K.isZero_of_isStrictlyGE a (a - 1) (by omega)
      rw [hzero _ (isZero_kernel_of_isZero _ hX₀), hzero _ hX₀, add_zero, add_zero] at hlow
      have key := hrel a (a + 1) (a + 1 + 1) rfl rfl
      rw [hlow] at key
      have hX : w (K.X a)
          = w (kernel (K.d (a + 1) (a + 1 + 1))) + w (K.homology a)
            - w (K.homology (a + 1)) := by
        rw [key]; abel
      have he : (((a + 1).negOnePow : ℤ)) = -((a.negOnePow : ℤ)) := by
        rw [Int.negOnePow_succ]; simp
      simp only [Finset.Icc_self, Finset.sum_singleton, hX, he]
      simp only [smul_add, smul_sub, neg_smul]
      abel
  | succ b hb ih =>
      have hins : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (b + 1) ∉ Finset.Icc a b := by simp
      have key := hrel (b + 1) (b + 1 + 1) (b + 1 + 1 + 1) rfl rfl
      have hX : w (K.X (b + 1))
          = w (kernel (K.d (b + 1 + 1) (b + 1 + 1 + 1)))
            + w (kernel (K.d (b + 1) (b + 1 + 1))) - w (K.homology (b + 1 + 1)) := by
        rw [key]; abel
      have he : (((b + 1 + 1).negOnePow : ℤ)) = -(((b + 1).negOnePow : ℤ)) := by
        rw [Int.negOnePow_succ]; simp
      rw [hins, Finset.sum_insert hnot, Finset.sum_insert hnot, ih, hX, he]
      simp only [smul_add, smul_sub, neg_smul]
      abel

/-- **The Euler–Poincaré telescoping.** Let `w` be a function on the objects of an abelian
category which vanishes on zero objects and satisfies, in every degree `j` of a cochain complex
`K`, the homology relation `w(ker dʲ) + w(ker dⁱ) = w(Hʲ K) + w(Kⁱ)` for `i + 1 = j`. If `K` is
strictly supported in degrees `a` to `b`, then over any finite range of degrees containing
`[a, b]` the alternating sum of the values of `w` on the terms equals the alternating sum of its
values on the cohomology objects.

This is the common engine of the Euler–Poincaré theorems: the homology relation holds for an
invariant additive on all short exact sequences, and also for an invariant of an
extension-closed subcategory when the boundaries and cohomology of `K` lie in that subcategory. -/
theorem sum_negOnePow_X_eq_sum_negOnePow_homology (hzero : ∀ X : A, IsZero X → w X = 0)
    (hrel : ∀ i j k : ℤ, i + 1 = j → j + 1 = k →
      w (kernel (K.d j k)) + w (kernel (K.d i j)) = w (K.homology j) + w (K.X i))
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • w (K.X n)
      = ∑ n ∈ s, ((n.negOnePow : ℤ)) • w (K.homology n) := by
  have hX : ∑ n ∈ s, ((n.negOnePow : ℤ)) • w (K.X n)
      = ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • w (K.X n) :=
    (Finset.sum_subset hs fun x _ hx => by
      rw [hzero _ (K.isZero_X_of_notMem_Icc a b hx), smul_zero]).symm
  have hH : ∑ n ∈ s, ((n.negOnePow : ℤ)) • w (K.homology n)
      = ∑ n ∈ Finset.Icc a b, ((n.negOnePow : ℤ)) • w (K.homology n) :=
    (Finset.sum_subset hs fun x _ hx => by
      rw [hzero _ (K.isZero_homology_of_notMem_Icc a b hx), smul_zero]).symm
  rw [hX, hH]
  rcases le_or_gt a b with hab | hab
  · rw [sum_negOnePow_Icc_aux K hzero hrel a b hab,
      hzero _ (K.isZero_of_isLE b (b + 1) (by omega)),
      hzero _ (isZero_kernel_of_isZero _ (K.isZero_of_isStrictlyLE b (b + 1) (by omega)))]
    simp
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, Finset.sum_empty]

end HomologicalComplex

namespace TauCeti

namespace AbelianK0

namespace AdditiveInvariant

variable {G : Type*} [AddCommGroup G] (v : AdditiveInvariant A G)

private theorem obj_eq_zero_of_isZero {X : A} (hX : IsZero X) : v.obj X = 0 := by
  have h : (ShortComplex.mk (𝟙 X) (𝟙 X) (hX.eq_of_src _ _)).ShortExact :=
    { exact := ShortComplex.exact_of_isZero_X₂ _ hX
      mono_f := inferInstance
      epi_g := inferInstance }
  exact left_eq_add.mp (v.map_shortExact h)

private theorem obj_eq_obj_kernel_add {Y Z : A} (p : Y ⟶ Z) [Epi p] :
    v.obj Y = v.obj (kernel p) + v.obj Z :=
  v.map_shortExact ((ExactStructure.abelian_conflation _).mp
    (ExactStructure.abelian_conflation_of_epi p))

private theorem obj_eq_add_obj_cokernel {X Y : A} (i : X ⟶ Y) [Mono i] :
    v.obj Y = v.obj X + v.obj (cokernel i) :=
  v.map_shortExact ((ExactStructure.abelian_conflation _).mp
    (ExactStructure.abelian_conflation_of_mono i))

/-- **The homology relation for an additive invariant.** For a short complex
`S = (X₁ ⟶ X₂ ⟶ X₃)` in an abelian category and an invariant `v` additive on short exact
sequences, `v(ker S.g) + v(ker S.f) = v(S.homology) + v(S.X₁)`.

Both sides count the boundaries `im S.f` once: the kernel of `S.g` is an extension of the homology
by them, and `X₁` is an extension of them by the kernel of `S.f`. -/
theorem obj_kernel_add_obj_kernel (S : ShortComplex A) :
    v.obj (kernel S.g) + v.obj (kernel S.f) = v.obj S.homology + v.obj S.X₁ := by
  have h1 : v.obj (kernel S.g)
      = v.obj (Abelian.image (kernel.lift S.g S.f S.zero))
        + v.obj (cokernel (kernel.lift S.g S.f S.zero)) :=
    obj_eq_obj_kernel_add v (cokernel.π (kernel.lift S.g S.f S.zero))
  have h2 : v.obj (cokernel (kernel.lift S.g S.f S.zero)) = v.obj S.homology :=
    v.map_iso S.homologyIsoCokernelLift.symm
  have h3 : v.obj S.X₁ = v.obj (kernel (kernel.lift S.g S.f S.zero))
      + v.obj (Abelian.coimage (kernel.lift S.g S.f S.zero)) :=
    obj_eq_add_obj_cokernel v (kernel.ι (kernel.lift S.g S.f S.zero))
  have h4 : v.obj (Abelian.coimage (kernel.lift S.g S.f S.zero))
      = v.obj (Abelian.image (kernel.lift S.g S.f S.zero)) :=
    v.map_iso (Abelian.coimageIsoImage _)
  have h5 : v.obj (kernel (kernel.lift S.g S.f S.zero)) = v.obj (kernel S.f) :=
    v.map_iso ((kernelCompMono _ (kernel.ι S.g)).symm ≪≫ kernelIsoOfEq (kernel.lift_ι _ _ _))
  rw [h1, h2, h3, h4, h5]
  abel

section CochainComplex

variable (K : CochainComplex A ℤ)

/-- **The degreewise homology relation for a cochain complex.** For consecutive degrees
`i + 1 = j` and `j + 1 = k`, the values of an additive invariant on the two cocycle objects around
degree `j` differ from its value on the cohomology at `j` by its value on the term in degree
`i`. -/
theorem obj_kernel_d_add_obj_kernel_d (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    v.obj (kernel (K.d j k)) + v.obj (kernel (K.d i j))
      = v.obj (K.homology j) + v.obj (K.X i) := by
  have h := obj_kernel_add_obj_kernel v (K.sc' i j k)
  rwa [v.map_iso (K.homologyIsoSc' i j k ((ComplexShape.up ℤ).prev_eq' hij)
    ((ComplexShape.up ℤ).next_eq' hjk)).symm] at h

/-- In the lowest degree where a bounded-below complex lives, the cocycles are the cohomology,
because there are no coboundaries. -/
theorem obj_kernel_d_eq_obj_homology (a : ℤ) [K.IsStrictlyGE a] :
    v.obj (kernel (K.d a (a + 1))) = v.obj (K.homology a) := by
  have h := obj_kernel_d_add_obj_kernel_d v K (a - 1) a (a + 1) (by omega) rfl
  have hX : IsZero (K.X (a - 1)) := K.isZero_of_isStrictlyGE a (a - 1) (by omega)
  rw [obj_eq_zero_of_isZero v (isZero_kernel_of_isZero _ hX), obj_eq_zero_of_isZero v hX] at h
  simpa using h

/-- **The Euler–Poincaré theorem for an additive invariant.** For a cochain complex that is
strictly supported in degrees `a` to `b`, any finite range of degrees containing `[a, b]`, and any
invariant additive on short exact sequences, the alternating sum of the values on the terms equals
the alternating sum of the values on the cohomology objects. -/
theorem sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology (a b : ℤ) [K.IsStrictlyGE a]
    [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.X n)
      = ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj (K.homology n) :=
  K.sum_negOnePow_X_eq_sum_negOnePow_homology (fun _ => obj_eq_zero_of_isZero v)
    (obj_kernel_d_add_obj_kernel_d v K) a b hs

end CochainComplex

end AdditiveInvariant

variable [EssentiallySmall.{w} A]

/-- The tautological additive invariant `X ↦ [X]` with values in abelian `K₀`, along which the
general Euler–Poincaré statements specialize to their `K₀` forms. -/
private noncomputable def ofInvariant : AdditiveInvariant A (AbelianK0 A) :=
  liftEquiv.symm (AddMonoidHom.id (AbelianK0 A))

@[simp] private lemma ofInvariant_obj (X : A) : (ofInvariant (A := A)).obj X = of X := by
  simp [ofInvariant]

/-- **The homology relation in abelian `K₀`.** For a short complex `S = (X₁ ⟶ X₂ ⟶ X₃)` in an
abelian category, `[ker S.g] + [ker S.f] = [S.homology] + [S.X₁]`. -/
theorem of_kernel_add_of_kernel (S : ShortComplex A) :
    (of (kernel S.g) : AbelianK0 A) + of (kernel S.f) = of S.homology + of S.X₁ := by
  simpa using AdditiveInvariant.obj_kernel_add_obj_kernel ofInvariant S

section CochainComplex

variable (K : CochainComplex A ℤ)

/-- The alternating class `∑ n ∈ s, (-1)ⁿ [Kⁿ]` of the terms of a cochain complex over a finite
set `s` of degrees. The set of degrees is data: the value is the truncation of the alternating sum
to `s`, and `TauCeti.AbelianK0.eulerChar_eq_eulerChar` shows that it stops depending on `s` once
`s` contains the support of a bounded complex. -/
noncomputable def eulerChar (s : Finset ℤ) : AbelianK0 A :=
  ∑ n ∈ s, ((n.negOnePow : ℤ)) • of (K.X n)

/-- The alternating class `∑ n ∈ s, (-1)ⁿ [Hⁿ K]` of the cohomology of a cochain complex over a
finite set `s` of degrees. -/
noncomputable def homologyEulerChar (s : Finset ℤ) : AbelianK0 A :=
  ∑ n ∈ s, ((n.negOnePow : ℤ)) • of (K.homology n)

@[simp] theorem eulerChar_empty : eulerChar K ∅ = 0 := Finset.sum_empty

@[simp] theorem homologyEulerChar_empty : homologyEulerChar K ∅ = 0 := Finset.sum_empty

@[simp] theorem eulerChar_insert {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    eulerChar K (insert n s) = ((n.negOnePow : ℤ)) • of (K.X n) + eulerChar K s :=
  Finset.sum_insert hn

@[simp] theorem homologyEulerChar_insert {s : Finset ℤ} {n : ℤ} (hn : n ∉ s) :
    homologyEulerChar K (insert n s)
      = ((n.negOnePow : ℤ)) • of (K.homology n) + homologyEulerChar K s :=
  Finset.sum_insert hn

section CohomologyBounded

variable (a b : ℤ) [K.IsGE a] [K.IsLE b]

/-- Enlarging the range of degrees beyond the support of the cohomology does not change the
alternating class of that cohomology.

Only the cohomology has to be bounded: `K.IsGE a` and `K.IsLE b` say that the cohomology of `K`
vanishes outside `[a, b]`. The terms `K.X n` may be nonzero in every degree, as they are for an
unbounded resolution. -/
theorem homologyEulerChar_eq_homologyEulerChar_Icc {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    homologyEulerChar K s = homologyEulerChar K (Finset.Icc a b) :=
  (Finset.sum_subset hs fun x _ hx => by
    rw [of_eq_zero_of_isZero
      (K.isZero_homology_of_notMem_Icc a b hx), smul_zero]).symm

/-- The alternating class of the cohomology of a complex with bounded cohomology does not depend
on the finite range of degrees over which it is summed. -/
theorem homologyEulerChar_eq_homologyEulerChar {s t : Finset ℤ} (hs : Finset.Icc a b ⊆ s)
    (ht : Finset.Icc a b ⊆ t) : homologyEulerChar K s = homologyEulerChar K t := by
  rw [homologyEulerChar_eq_homologyEulerChar_Icc K a b hs,
    homologyEulerChar_eq_homologyEulerChar_Icc K a b ht]

end CohomologyBounded

section Bounded

variable (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

/-- Enlarging the range of degrees beyond the support of a bounded complex does not change its
Euler characteristic. -/
theorem eulerChar_eq_eulerChar_Icc {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    eulerChar K s = eulerChar K (Finset.Icc a b) :=
  (Finset.sum_subset hs fun x _ hx => by
    rw [of_eq_zero_of_isZero
      (K.isZero_X_of_notMem_Icc a b hx), smul_zero]).symm

/-- The Euler characteristic of a bounded complex does not depend on the finite range of degrees
over which it is summed, as long as that range contains the support. -/
theorem eulerChar_eq_eulerChar {s t : Finset ℤ} (hs : Finset.Icc a b ⊆ s)
    (ht : Finset.Icc a b ⊆ t) : eulerChar K s = eulerChar K t := by
  rw [eulerChar_eq_eulerChar_Icc K a b hs, eulerChar_eq_eulerChar_Icc K a b ht]

/-- **The Euler–Poincaré theorem in abelian `K₀`.** For a cochain complex that is strictly
supported in degrees `a` to `b`, and any finite range of degrees containing `[a, b]`, the
alternating sum of the classes of the terms equals the alternating sum of the classes of the
cohomology objects. -/
theorem eulerChar_eq_homologyEulerChar {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    eulerChar K s = homologyEulerChar K s := by
  simpa [eulerChar, homologyEulerChar] using
    AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology ofInvariant K a b hs

/-- A bounded exact complex has vanishing Euler characteristic. -/
theorem eulerChar_eq_zero_of_exactAt (hK : ∀ n : ℤ, K.ExactAt n) {s : Finset ℤ}
    (hs : Finset.Icc a b ⊆ s) : eulerChar K s = 0 := by
  rw [eulerChar_eq_homologyEulerChar K a b hs]
  exact Finset.sum_eq_zero fun n _ => by
    rw [of_eq_zero_of_isZero (hK n).isZero_homology, smul_zero]

end Bounded

section QuasiIso

variable {K} {L : CochainComplex A ℤ} (f : K ⟶ L) [QuasiIso f]

include f in
/-- A quasi-isomorphism preserves the alternating class of the cohomology, in any range of
degrees. -/
theorem homologyEulerChar_eq_of_quasiIso (s : Finset ℤ) :
    homologyEulerChar K s = homologyEulerChar L s :=
  Finset.sum_congr rfl fun n _ => by
    have : IsIso (HomologicalComplex.homologyMap f n) :=
      (quasiIsoAt_iff_isIso_homologyMap f n).mp inferInstance
    rw [of_congr (asIso (HomologicalComplex.homologyMap f n))]

include f in
/-- **The Euler characteristic is a quasi-isomorphism invariant.** Two bounded complexes joined by
a quasi-isomorphism have the same alternating class of terms, over any finite range of degrees
containing both supports; this is what makes the Euler characteristic a function of the image of
the complex in the derived category. -/
theorem eulerChar_eq_of_quasiIso (aK bK aL bL : ℤ) [K.IsStrictlyGE aK] [K.IsStrictlyLE bK]
    [L.IsStrictlyGE aL] [L.IsStrictlyLE bL] {s : Finset ℤ} (hK : Finset.Icc aK bK ⊆ s)
    (hL : Finset.Icc aL bL ⊆ s) : eulerChar K s = eulerChar L s := by
  rw [eulerChar_eq_homologyEulerChar K aK bK hK, homologyEulerChar_eq_of_quasiIso f s,
    ← eulerChar_eq_homologyEulerChar L aL bL hL]

end QuasiIso

end CochainComplex

end AbelianK0

section BoundariesCycles

variable (K : CochainComplex A ℤ)

/-- The inclusion of the boundaries `im dⁱ` into the cocycles `ker dʲ`. -/
private noncomputable def boundariesToCycles (i j k : ℤ) :
    Abelian.image (K.d i j) ⟶ kernel (K.d j k) :=
  kernel.lift _ (Abelian.image.ι (K.d i j)) (by
    rw [← cancel_epi (Abelian.factorThruImage (K.d i j)), ← Category.assoc, Abelian.image.fac,
      K.d_comp_d, comp_zero])

private instance (i j k : ℤ) : Mono (boundariesToCycles K i j k) :=
  mono_of_mono_fac (kernel.lift_ι _ _ _)

private lemma kernelLift_d_eq (i j k : ℤ) :
    kernel.lift (K.d j k) (K.d i j) (K.d_comp_d i j k)
      = Abelian.factorThruImage (K.d i j) ≫ boundariesToCycles K i j k := by
  ext
  simp [boundariesToCycles]

/-- The cokernel of the inclusion of the boundaries into the cocycles is the cohomology. -/
private noncomputable def cokernelBoundariesToCyclesIso (i j k : ℤ) (hij : i + 1 = j)
    (hjk : j + 1 = k) : cokernel (boundariesToCycles K i j k) ≅ K.homology j :=
  (cokernelEpiComp (Abelian.factorThruImage (K.d i j)) (boundariesToCycles K i j k)).symm ≪≫
    cokernelIsoOfEq (kernelLift_d_eq K i j k).symm ≪≫
    (K.sc' i j k).homologyIsoCokernelLift.symm ≪≫
    (K.homologyIsoSc' i j k ((ComplexShape.up ℤ).prev_eq' hij)
      ((ComplexShape.up ℤ).next_eq' hjk)).symm

/-- The kernel of the projection of `Kⁱ` onto the boundaries `im dⁱ` is the cocycles
`ker dⁱ`. -/
private noncomputable def kernelFactorThruImageIso (i j : ℤ) :
    kernel (K.d i j) ≅ kernel (Abelian.factorThruImage (K.d i j)) :=
  kernelIsoOfEq (Abelian.image.fac (K.d i j)).symm ≪≫ kernelCompMono _ _

end BoundariesCycles

namespace ExactStructure.IsExtensionClosed

variable {P : ObjectProperty A} [P.ContainsZero]
  (hP : (ExactStructure.abelian A).IsExtensionClosed P) {K : CochainComplex A ℤ}

include hP in
/-- The cocycles are an extension of the cohomology by the boundaries, so they lie in `P` as soon
as the boundaries and the cohomology do. -/
private lemma prop_kernel_d_of_rel {i j k : ℤ} (hij : i + 1 = j) (hjk : j + 1 = k)
    (hB : P (Abelian.image (K.d i j))) (hH : P (K.homology j)) : P (kernel (K.d j k)) :=
  have := hP.isClosedUnderIsomorphisms
  hP.prop_X₂ (ExactStructure.abelian_conflation_of_mono (boundariesToCycles K i j k)) hB
    (P.prop_of_iso (cokernelBoundariesToCyclesIso K i j k hij hjk).symm hH)

include hP in
/-- If the boundaries `im dⁿ` and the cohomology objects of a cochain complex lie in an
extension-closed property, then so do its cocycles `ker dⁿ`, which are extensions of the
cohomology by the boundaries. -/
theorem prop_kernel_d (hB : ∀ n, P (Abelian.image (K.d n (n + 1))))
    (hH : ∀ n, P (K.homology n)) (n : ℤ) : P (kernel (K.d n (n + 1))) := by
  have hB' := hB (n - 1)
  rw [show n - 1 + 1 = n by omega] at hB'
  exact hP.prop_kernel_d_of_rel (by omega) rfl hB' (hH n)

include hP in
/-- If the boundaries `im dⁿ` and the cohomology objects of a cochain complex lie in an
extension-closed property, then so do its terms: `Kⁿ` is an extension of the boundaries
`im dⁿ` by the cocycles `ker dⁿ`. -/
theorem prop_X (hB : ∀ n, P (Abelian.image (K.d n (n + 1))))
    (hH : ∀ n, P (K.homology n)) (n : ℤ) : P (K.X n) :=
  have := hP.isClosedUnderIsomorphisms
  hP.prop_X₂ (ExactStructure.abelian_conflation_of_epi (Abelian.factorThruImage (K.d n (n + 1))))
    (P.prop_of_iso (kernelFactorThruImageIso K n (n + 1)) (hP.prop_kernel_d hB hH n)) (hB n)

end ExactStructure.IsExtensionClosed

namespace ExactK0

variable {P : ObjectProperty A} [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  {hP : (ExactStructure.abelian A).IsExtensionClosed P}

namespace AdditiveInvariant

variable {G : Type*} [AddCommGroup G]
  (v : AdditiveInvariant ((ExactStructure.abelian A).fullSubcategory P hP) G)

open Classical in
/-- The values of an additive invariant of the subcategory, extended by zero to the objects of
`A` outside `P`. Only its values on objects of `P` are ever used. -/
private noncomputable def extend (X : A) : G :=
  if h : P X then v.obj ⟨X, h⟩ else 0

private lemma extend_of {X : A} (h : P X) : extend v X = v.obj ⟨X, h⟩ := by
  simp [extend, h]

private lemma extend_eq_zero_of_isZero {X : A} (hX : IsZero X) : extend v X = 0 := by
  by_cases h : P X
  · rw [extend_of v h]
    exact v.obj_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero P.ι ⟨X, h⟩ hX)
  · simp [extend, h]

private lemma extend_congr {X Y : A} (e : X ≅ Y) (h : P X) : extend v X = extend v Y := by
  have := hP.isClosedUnderIsomorphisms
  rw [extend_of v h, extend_of v (P.prop_of_iso e h)]
  exact v.map_iso (P.isoMk e)

/-- The extended invariant is additive on the short exact sequences of `A` whose outer terms lie
in `P`; the middle term then lies in `P` by extension closure. -/
private lemma extend_X₂ {S : ShortComplex A} (hS : S.ShortExact) (h₁ : P S.X₁) (h₃ : P S.X₃) :
    extend v S.X₂ = extend v S.X₁ + extend v S.X₃ := by
  have h₂ := hP.prop_X₂ ((ExactStructure.abelian_conflation S).mpr hS) h₁ h₃
  rw [extend_of v h₁, extend_of v h₂, extend_of v h₃]
  let S' : ShortComplex P.FullSubcategory := ShortComplex.mk
    (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : P.FullSubcategory) ⟶ ⟨S.X₂, h₂⟩)
    (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : P.FullSubcategory) ⟶ ⟨S.X₃, h₃⟩)
    (by ext; exact S.zero)
  have hS' : ((ExactStructure.abelian A).fullSubcategory P hP).Conflation S' := by
    rw [ExactStructure.fullSubcategory_conflation_iff, ExactStructure.abelian_conflation]
    exact hS
  exact v.map_conflation hS'

variable {K : CochainComplex A ℤ}

/-- The homology relation `[ker dʲ] + [ker dⁱ] = [Hʲ K] + [Kⁱ]` for an invariant of the
subcategory, from the two short exact sequences `ker dⁱ ↪ Kⁱ ↠ im dⁱ` and
`im dⁱ ↪ ker dʲ ↠ Hʲ K`, whose terms all lie in `P`. -/
private lemma extend_kernel_d_add_extend_kernel_d (hB : ∀ n, P (Abelian.image (K.d n (n + 1))))
    (hH : ∀ n, P (K.homology n)) (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    extend v (kernel (K.d j k)) + extend v (kernel (K.d i j))
      = extend v (K.homology j) + extend v (K.X i) := by
  subst hij hjk
  have := hP.isClosedUnderIsomorphisms
  have hZ := hP.prop_kernel_d hB hH i
  have hC := P.prop_of_iso (cokernelBoundariesToCyclesIso K _ _ _ rfl rfl).symm (hH (i + 1))
  -- `ker dʲ` is an extension of the cohomology by the boundaries
  have h₁ := extend_X₂ v
    ((ExactStructure.abelian_conflation _).mp
      (ExactStructure.abelian_conflation_of_mono (boundariesToCycles K i (i + 1) (i + 1 + 1))))
    (hB i) hC
  -- `Kⁱ` is an extension of the boundaries by `ker dⁱ`
  have h₂ := extend_X₂ v
    ((ExactStructure.abelian_conflation _).mp
      (ExactStructure.abelian_conflation_of_epi (Abelian.factorThruImage (K.d i (i + 1)))))
    (P.prop_of_iso (kernelFactorThruImageIso K i (i + 1)) hZ) (hB i)
  dsimp only at h₁ h₂
  rw [h₁, h₂, extend_congr v (cokernelBoundariesToCyclesIso K _ _ _ rfl rfl) hC,
    ← extend_congr v (kernelFactorThruImageIso K i (i + 1)) hZ]
  abel

/-- **The Euler–Poincaré theorem in an extension-closed subcategory.** Let `P` be an
extension-closed full subcategory of an abelian category `A` with its induced exact structure,
and let `K` be a cochain complex strictly supported in degrees `a` to `b` whose boundaries
`im dⁿ` and cohomology objects lie in `P`; its cocycles and terms then lie in `P` as well
(`TauCeti.ExactStructure.IsExtensionClosed.prop_X`). For any invariant of the subcategory
additive on its conflations and any finite range of degrees containing `[a, b]`, the alternating
sum of the values on the terms equals the alternating sum of the values on the cohomology
objects. -/
theorem sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology
    (hB : ∀ n, P (Abelian.image (K.d n (n + 1)))) (hH : ∀ n, P (K.homology n))
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj ⟨K.X n, hP.prop_X hB hH n⟩
      = ∑ n ∈ s, ((n.negOnePow : ℤ)) • v.obj ⟨K.homology n, hH n⟩ := by
  simp only [← extend_of v]
  exact K.sum_negOnePow_X_eq_sum_negOnePow_homology (fun _ => extend_eq_zero_of_isZero v)
    (extend_kernel_d_add_extend_kernel_d v hB hH) a b hs

end AdditiveInvariant

variable (hP) in
/-- **The Euler–Poincaré theorem in exact `K₀` of an extension-closed subcategory.** Let `P` be
an extension-closed full subcategory of an abelian category `A`, with its induced exact
structure, and let `K` be a cochain complex strictly supported in degrees `a` to `b` whose
boundaries `im dⁿ` and cohomology objects lie in `P`, so that its terms do too. Then over any
finite range of degrees containing `[a, b]`,

```text
∑ n, (-1)ⁿ [Kⁿ] = ∑ n, (-1)ⁿ [Hⁿ K]
```

in the exact `K₀` of the subcategory. This is the analogue of
`TauCeti.AbelianK0.eulerChar_eq_homologyEulerChar` for the subcategory; the comparison stays at
the level of the complex, and no derived category of the subcategory is involved. -/
theorem sum_negOnePow_of_X_eq_sum_negOnePow_of_homology [EssentiallySmall.{w} P.FullSubcategory]
    (K : CochainComplex A ℤ) (hB : ∀ n, P (Abelian.image (K.d n (n + 1))))
    (hH : ∀ n, P (K.homology n))
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] {s : Finset ℤ} (hs : Finset.Icc a b ⊆ s) :
    ∑ n ∈ s, ((n.negOnePow : ℤ)) • (of ⟨K.X n, hP.prop_X hB hH n⟩ :
        ExactK0 ((ExactStructure.abelian A).fullSubcategory P hP))
      = ∑ n ∈ s, ((n.negOnePow : ℤ)) • of ⟨K.homology n, hH n⟩ := by
  simpa using AdditiveInvariant.sum_negOnePow_obj_X_eq_sum_negOnePow_obj_homology
    (liftEquiv.symm (AddMonoidHom.id
      (ExactK0.{w} ((ExactStructure.abelian A).fullSubcategory P hP)))) hB hH a b hs

end ExactK0

end TauCeti
