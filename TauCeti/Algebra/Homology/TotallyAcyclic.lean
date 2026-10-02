/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Totally acyclic complexes and Gorenstein-projective modules

Let `A` be a ring. A cochain complex `P` of `A`-modules is **totally acyclic** when every term
`Pⁿ` is finitely generated and projective, `P` is acyclic, and the dual complex
`Hom_A(P, A)` is acyclic as well. A module is **Gorenstein-projective** when it is isomorphic to
the degree-zero cycles `Z⁰(P)` of a totally acyclic complex `P`; the complex is then a *complete
resolution* of the module.

Right modules over a ring `R` are the case `A = Rᵐᵒᵖ`, where `Hom_{Rᵐᵒᵖ}(P, Rᵐᵒᵖ)` is the usual
`R`-dual of a complex of right `R`-modules.

The dual of `Pⁿ` is `Pⁿ →ₗ[A] A`, which is a right `A`-module, that is, an `Aᵐᵒᵖ`-module, through
right multiplication on the target. The dual differential `Hom_A(Pᵏ, A) → Hom_A(Pʲ, A)` is
precomposition with `d : Pʲ ⟶ Pᵏ`, which is `LinearMap.lcomp Aᵐᵒᵖ A`. Dual acyclicity is
therefore recorded as exactness of the composable pairs of these precomposition maps.

Finite generation is required of *every* term of the complex. It is not implied by finite
generation of a single module of cycles: adding a contractible complex `F --𝟙--> F` on an
infinitely generated free module `F` away from degree zero preserves acyclicity, dual acyclicity
and `Z⁰(P)`.

## Main definitions

* `CochainComplex.IsTotallyAcyclic`: a totally acyclic complex of finitely generated projective
  modules.
* `TauCeti.IsGorensteinProjective`: the modules isomorphic to the degree-zero cycles of a totally
  acyclic complex.
* `TauCeti.alternatingMulRightComplex`: the two-periodic complex `⋯ → A --·a--> A --·b--> A → ⋯`
  for `a * b = 0` and `b * a = 0`.

## Main results

* `CochainComplex.IsTotallyAcyclic.of_iso` and `CochainComplex.IsTotallyAcyclic.shift`: total
  acyclicity is invariant under isomorphisms and shifts of complexes.
* `CochainComplex.IsTotallyAcyclic.isGorensteinProjective_cycles`: the cycles of a totally
  acyclic complex in *every* degree are Gorenstein-projective, so the syzygies and cosyzygies of a
  Gorenstein-projective module in a complete resolution are Gorenstein-projective.
* `TauCeti.IsGorensteinProjective.finite`: Gorenstein-projective modules are finitely generated.
* `TauCeti.isGorensteinProjective_of_projective`: a finitely generated projective module is
  Gorenstein-projective, with complete resolution `M --𝟙--> M` in degrees `-1` and `0`.
* `TauCeti.isTotallyAcyclic_alternatingMulRightComplex` and
  `TauCeti.isGorensteinProjective_span_singleton`: for an exact pair of zero-divisors `a, b`, the
  two-periodic complex `⋯ → A --·a--> A --·b--> A → ⋯` is totally acyclic, so the left ideal `A b`
  is Gorenstein-projective. For `A = k[x]/(xⁿ)`, `a = xⁱ` and `b = xⁿ⁻ⁱ`, this is the two-periodic
  complete resolution of `A b ≅ A/(xⁱ)`; such modules need not be projective.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Section 4.
* Edgar E. Enochs and Overtoun M. G. Jenda, *Relative Homological Algebra*, de Gruyter
  Expositions in Mathematics **30** (2000), Section 10.2.
* Inês B. Henriques and Liana M. Sega, *Free resolutions over short Gorenstein local rings*,
  Mathematische Zeitschrift **267** (2011), 645–663: exact pairs of zero-divisors.
-/

public section

open CategoryTheory Limits

universe v u

namespace CochainComplex

variable {A : Type u} [Ring A]

/-- A cochain complex `P` of `A`-modules is **totally acyclic** when its terms are finitely
generated projective modules, it is acyclic, and its `A`-dual `Hom_A(P, A)` is acyclic: for
`i + 1 = j` and `j + 1 = k`, the precomposition maps
`Hom_A(Pᵏ, A) → Hom_A(Pʲ, A) → Hom_A(Pⁱ, A)` are exact. -/
structure IsTotallyAcyclic (P : CochainComplex (ModuleCat.{v} A) ℤ) : Prop where
  /-- Every term is a finitely generated module. -/
  finite (n : ℤ) : Module.Finite A (P.X n)
  /-- Every term is a projective module. -/
  projective (n : ℤ) : Projective (P.X n)
  /-- The complex is acyclic. -/
  acyclic : P.Acyclic
  /-- The `A`-dual of the complex is acyclic. -/
  exact_dual (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    Function.Exact (LinearMap.lcomp Aᵐᵒᵖ A (P.d j k).hom)
      (LinearMap.lcomp Aᵐᵒᵖ A (P.d i j).hom)

namespace IsTotallyAcyclic

variable {P : CochainComplex (ModuleCat.{v} A) ℤ}

/-- Total acyclicity is invariant under isomorphisms of complexes. -/
theorem of_iso (hP : P.IsTotallyAcyclic) {Q : CochainComplex (ModuleCat.{v} A) ℤ} (e : P ≅ Q) :
    Q.IsTotallyAcyclic where
  finite n :=
    have := hP.finite n
    Module.Finite.equiv (HomologicalComplex.Hom.isoApp e n).toLinearEquiv
  projective n := Projective.of_iso (HomologicalComplex.Hom.isoApp e n) (hP.projective n)
  acyclic n := (hP.acyclic n).of_iso e
  exact_dual i j k hij hjk := by
    let δ (n : ℤ) := LinearEquiv.congrLeft A Aᵐᵒᵖ (HomologicalComplex.Hom.isoApp e n).toLinearEquiv
    have hδ (p q : ℤ) : LinearMap.lcomp Aᵐᵒᵖ A (Q.d p q).hom ∘ₗ (δ q).toLinearMap =
        (δ p).toLinearMap ∘ₗ LinearMap.lcomp Aᵐᵒᵖ A (P.d p q).hom := by
      ext φ x
      have h := congr(φ ($(congrArg ModuleCat.Hom.hom (e.inv.comm p q)) x))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
      simp [δ, h]
    exact Function.Exact.of_ladder_linearEquiv_of_exact (hδ j k) (hδ i j)
      (hP.exact_dual i j k hij hjk)

/-- A shift of a totally acyclic complex is totally acyclic. -/
theorem shift (hP : P.IsTotallyAcyclic) (m : ℤ) : (P⟦m⟧).IsTotallyAcyclic where
  finite n := hP.finite (n + m)
  projective n := hP.projective (n + m)
  acyclic := (P.acyclic_shift_iff m).2 hP.acyclic
  exact_dual i j k hij hjk := by
    have h := hP.exact_dual (i + m) (j + m) (k + m) (by lia) (by lia)
    simp only [shiftFunctor_obj_d']
    rcases Int.units_eq_one_or m.negOnePow with hm | hm
    · simpa [hm] using h
    · have e {X Y : ModuleCat.{v} A} (f : X ⟶ Y) :
          LinearMap.lcomp Aᵐᵒᵖ A ((-1 : ℤˣ) • f).hom = -LinearMap.lcomp Aᵐᵒᵖ A f.hom := by
        ext; simp
      rw [hm, e, e]
      exact Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := .refl _ _) (e₂ := .neg _)
        (e₃ := .refl _ _) (by ext; simp) (by ext; simp) h

end IsTotallyAcyclic

end CochainComplex

namespace TauCeti

variable (A : Type u) [Ring A]

/-- A module `M` is **Gorenstein-projective** when it is isomorphic to the degree-zero cycles
`Z⁰(P)` of a totally acyclic complex `P`, a *complete resolution* of `M`. -/
def IsGorensteinProjective : ObjectProperty (ModuleCat.{v} A) := fun M ↦
  ∃ P : CochainComplex (ModuleCat.{v} A) ℤ, P.IsTotallyAcyclic ∧ Nonempty (P.cycles 0 ≅ M)

variable {A}

/-- The defining property of a Gorenstein-projective module: it has a complete resolution. -/
lemma isGorensteinProjective_iff (M : ModuleCat.{v} A) :
    IsGorensteinProjective A M ↔
      ∃ P : CochainComplex (ModuleCat.{v} A) ℤ, P.IsTotallyAcyclic ∧ Nonempty (P.cycles 0 ≅ M) :=
  Iff.rfl

instance : (IsGorensteinProjective.{v} A).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨P, hP, ⟨e'⟩⟩ ↦ ⟨P, hP, ⟨e' ≪≫ e⟩⟩

/-- A Gorenstein-projective module is finitely generated: the degree-zero cycles of an acyclic
complex are a quotient of the term in degree `-1`. -/
theorem IsGorensteinProjective.finite {M : ModuleCat.{v} A} (hM : IsGorensteinProjective A M) :
    Module.Finite A M := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hM
  have : Module.Finite A (P.sc 0).X₁ := hP.finite _
  have hepi : Epi (P.sc 0).toCycles :=
    (ShortComplex.exact_iff_epi_toCycles _).1 (hP.acyclic 0)
  have : Module.Finite A (P.cycles 0) :=
    Module.Finite.of_surjective _ ((ModuleCat.epi_iff_surjective _).1 hepi)
  exact Module.Finite.equiv e.toLinearEquiv

end TauCeti

namespace CochainComplex.IsTotallyAcyclic

variable {A : Type u} [Ring A] {P : CochainComplex (ModuleCat.{v} A) ℤ}

/-- The cycles of a totally acyclic complex in any degree `n` are Gorenstein-projective: the
shift `P⟦n⟧` is a complete resolution of `Zⁿ(P)`. -/
theorem isGorensteinProjective_cycles (hP : P.IsTotallyAcyclic) (n : ℤ) :
    TauCeti.IsGorensteinProjective A (P.cycles n) :=
  ⟨P⟦n⟧, hP.shift n, ⟨P.shiftCyclesIso n 0 n (add_zero n)⟩⟩

end CochainComplex.IsTotallyAcyclic

namespace TauCeti

variable {A : Type u} [Ring A]

section Disk

variable (M : ModuleCat.{v} A)

/-- The relation `-1 → 0` in the shape of cochain complexes. -/
private lemma rel_neg_one_zero : (ComplexShape.up ℤ).Rel (-1) 0 := by simp

/-- The complex `M --𝟙--> M` concentrated in degrees `-1` and `0`. -/
private noncomputable abbrev disk : CochainComplex (ModuleCat.{v} A) ℤ :=
  HomologicalComplex.double (𝟙 M) rel_neg_one_zero

private lemma isIso_disk_d : IsIso ((disk M).d (-1) 0) := by
  rw [HomologicalComplex.double_d _ _ (by decide)]
  infer_instance

private lemma disk_d_eq_zero (j k : ℤ) (hj : j ≠ -1) : (disk M).d j k = 0 :=
  HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hj

private lemma isZero_disk_X (n : ℤ) (h₀ : n ≠ -1) (h₁ : n ≠ 0) : IsZero ((disk M).X n) :=
  HomologicalComplex.isZero_double_X _ _ _ h₀ h₁

private lemma isTotallyAcyclic_disk [Module.Finite A M] [Projective M] :
    (disk M).IsTotallyAcyclic where
  finite n := by
    by_cases h₀ : n = -1
    · subst h₀
      exact Module.Finite.equiv
        (HomologicalComplex.doubleXIso₀ (𝟙 M) rel_neg_one_zero).symm.toLinearEquiv
    by_cases h₁ : n = 0
    · subst h₁
      exact Module.Finite.equiv
        (HomologicalComplex.doubleXIso₁ (𝟙 M) rel_neg_one_zero (by decide)).symm.toLinearEquiv
    have := ModuleCat.subsingleton_of_isZero (isZero_disk_X M n h₀ h₁)
    infer_instance
  projective n := by
    by_cases h₀ : n = -1
    · subst h₀
      exact Projective.of_iso (HomologicalComplex.doubleXIso₀ (𝟙 M) rel_neg_one_zero).symm
        inferInstance
    by_cases h₁ : n = 0
    · subst h₁
      exact Projective.of_iso
        (HomologicalComplex.doubleXIso₁ (𝟙 M) rel_neg_one_zero (by decide)).symm inferInstance
    exact (isZero_disk_X M n h₀ h₁).projective
  acyclic n := by
    have := isIso_disk_d M
    by_cases h₀ : n = -1
    · subst h₀
      rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
        ShortComplex.exact_iff_mono _ (disk_d_eq_zero M _ _ (by decide))]
      exact inferInstanceAs (Mono ((disk M).d (-1) 0))
    by_cases h₁ : n = 0
    · subst h₁
      rw [HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
        ShortComplex.exact_iff_epi _ (disk_d_eq_zero M _ _ (by decide))]
      exact inferInstanceAs (Epi ((disk M).d (-1) 0))
    exact HomologicalComplex.ExactAt.of_isZero (isZero_disk_X M n h₀ h₁)
  exact_dual i j k hij hjk := by
    have := isIso_disk_d M
    by_cases h₀ : j = -1
    · subst h₀
      obtain rfl : k = 0 := by lia
      have h0 : LinearMap.lcomp Aᵐᵒᵖ A ((disk M).d i (-1)).hom = 0 := by
        ext; simp [disk_d_eq_zero M i _ (by lia)]
      rw [h0, LinearMap.exact_zero_iff_surjective]
      intro y
      exact ⟨y ∘ₗ (inv ((disk M).d (-1) 0)).hom, by ext; simp⟩
    by_cases h₁ : j = 0
    · subst h₁
      obtain rfl : i = -1 := by lia
      have h0 : LinearMap.lcomp Aᵐᵒᵖ A ((disk M).d 0 k).hom = 0 := by
        ext; simp [disk_d_eq_zero M 0 _ (by lia)]
      rw [h0, LinearMap.exact_zero_iff_injective]
      exact LinearMap.lcomp_injective_of_surjective _
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    have := ModuleCat.subsingleton_of_isZero (isZero_disk_X M j h₀ h₁)
    intro y
    rw [Subsingleton.elim y 0]
    exact ⟨fun _ ↦ ⟨0, map_zero _⟩, fun _ ↦ map_zero _⟩

end Disk

/-- A finitely generated projective module `M` is Gorenstein-projective: the complex
`M --𝟙--> M`, concentrated in degrees `-1` and `0`, is a complete resolution of `M`. -/
theorem isGorensteinProjective_of_projective (M : ModuleCat.{v} A) [Module.Finite A M]
    [Projective M] : IsGorensteinProjective A M :=
  ⟨disk M, isTotallyAcyclic_disk M, ⟨(disk M).iCyclesIso 0 1 (by simp)
    (disk_d_eq_zero M _ _ (by decide)) ≪≫
      HomologicalComplex.doubleXIso₁ (𝟙 M) rel_neg_one_zero (by decide)⟩⟩

section ExactPair

variable (a b : A)

/-- The two-periodic complex `⋯ → A --·a--> A --·b--> A --·a--> ⋯` of free `A`-modules of rank
one: every term is `A`, and the differential out of degree `n` is right multiplication by `a` for
even `n` and by `b` for odd `n`. -/
noncomputable abbrev alternatingMulRightComplex (hab : a * b = 0) (hba : b * a = 0) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.of (fun _ ↦ ModuleCat.of A A)
    (fun n ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton A A (if Even n then a else b)))
    (fun n ↦ by
      ext
      by_cases hn : Even n
      · simp [hn, hab]
      · simp [hn, hba])

variable {a b} (hab : a * b = 0) (hba : b * a = 0)

/-- Every term of `TauCeti.alternatingMulRightComplex a b` is `A`. -/
lemma alternatingMulRightComplex_X (n : ℤ) :
    (alternatingMulRightComplex a b hab hba).X n = ModuleCat.of A A :=
  rfl

/-- The differential of `TauCeti.alternatingMulRightComplex a b` out of degree `i` is right
multiplication by `a` for even `i` and by `b` for odd `i`. -/
lemma alternatingMulRightComplex_d {i j : ℤ} (h : i + 1 = j) :
    (alternatingMulRightComplex a b hab hba).d i j =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A A (if Even i then a else b)) := by
  subst h
  simp [alternatingMulRightComplex]

@[simp]
lemma alternatingMulRightComplex_d_apply {i j : ℤ} (h : i + 1 = j) (r : A) :
    ((alternatingMulRightComplex a b hab hba).d i j).hom r = r * if Even i then a else b := by
  rw [alternatingMulRightComplex_d _ _ h]
  by_cases hi : Even i <;> simp [hi]

variable {hab hba} in
/-- Let `a, b : A` be an *exact pair of zero-divisors*: the left annihilator of `a` is `A b`, the
left annihilator of `b` is `A a`, the right annihilator of `a` is `b A` and the right annihilator
of `b` is `a A`. Then the two-periodic complex `⋯ → A --·a--> A --·b--> A → ⋯` is totally
acyclic. For example, over `k[x]/(xⁿ)` the pair `a = xⁱ`, `b = xⁿ⁻ⁱ` with `0 < i < n` is exact. -/
theorem isTotallyAcyclic_alternatingMulRightComplex
    (hla : ∀ r : A, r * a = 0 ↔ ∃ t, t * b = r) (hlb : ∀ r : A, r * b = 0 ↔ ∃ t, t * a = r)
    (hra : ∀ s : A, a * s = 0 ↔ ∃ t, b * t = s) (hrb : ∀ s : A, b * s = 0 ↔ ∃ t, a * t = s) :
    (alternatingMulRightComplex a b hab hba).IsTotallyAcyclic where
  finite _ := inferInstanceAs (Module.Finite A A)
  projective _ := inferInstanceAs (Projective (ModuleCat.of A A))
  acyclic n := by
    rw [HomologicalComplex.exactAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro (r : A) hr
    have hr' : r * (if Even n then a else b) = 0 :=
      (alternatingMulRightComplex_d_apply hab hba rfl r).symm.trans hr
    have hd (t : A) := alternatingMulRightComplex_d_apply hab hba (sub_add_cancel n 1) t
    by_cases hn : Even n
    · have hn' : ¬Even (n - 1) := by rwa [Int.even_sub_one, not_not]
      obtain ⟨t, ht⟩ := (hla r).1 (by simpa only [hn, ↓reduceIte] using hr')
      exact ⟨t, (hd t).trans (by simp only [hn', ↓reduceIte, ht])⟩
    · have hn' : Even (n - 1) := Int.even_sub_one.2 hn
      obtain ⟨t, ht⟩ := (hlb r).1 (by simpa only [hn, ↓reduceIte] using hr')
      exact ⟨t, (hd t).trans (by simp only [hn', ↓reduceIte, ht])⟩
  exact_dual i j k hij hjk := by
    rw [alternatingMulRightComplex_d _ _ hij, alternatingMulRightComplex_d _ _ hjk,
      ModuleCat.hom_ofHom, ModuleCat.hom_ofHom]
    -- Under `ψ ↦ ψ 1`, the dual of `A --·c--> A --·c'--> A` is left multiplication by `c` and
    -- by `c'`, which is exact when the right annihilator of `c'` is `c A`.
    have key {c c' : A} (h : ∀ s : A, c' * s = 0 ↔ ∃ t, c * t = s) :
        Function.Exact (LinearMap.lcomp Aᵐᵒᵖ A (LinearMap.toSpanSingleton A A c))
          (LinearMap.lcomp Aᵐᵒᵖ A (LinearMap.toSpanSingleton A A c')) := by
      intro ψ
      constructor
      · intro hψ
        have : c' * ψ 1 = 0 := by
          rw [← smul_eq_mul, ← map_smul, smul_eq_mul]
          simpa using congr($hψ 1)
        obtain ⟨t, ht⟩ := (h _).1 this
        exact ⟨LinearMap.toSpanSingleton A A t, LinearMap.ext_ring (by simp [ht])⟩
      · rintro ⟨φ, rfl⟩
        have : c' * c = 0 := (h c).2 ⟨1, mul_one c⟩
        exact LinearMap.ext_ring (by simp [this])
    obtain rfl : i = j - 1 := by lia
    by_cases hj : Even j
    · have hj' : ¬Even (j - 1) := by rwa [Int.even_sub_one, not_not]
      simpa only [hj, hj', ↓reduceIte] using key hrb
    · have hj' : Even (j - 1) := Int.even_sub_one.2 hj
      simpa only [hj, hj', ↓reduceIte] using key hra

variable {hab hba} in
/-- For an exact pair of zero-divisors `a, b : A`, the left ideal `A b` is Gorenstein-projective,
with complete resolution the two-periodic complex `⋯ → A --·a--> A --·b--> A → ⋯`, whose
degree-zero cycles are the left annihilator `A b` of `a`. -/
theorem isGorensteinProjective_span_singleton
    (hla : ∀ r : A, r * a = 0 ↔ ∃ t, t * b = r) (hlb : ∀ r : A, r * b = 0 ↔ ∃ t, t * a = r)
    (hra : ∀ s : A, a * s = 0 ↔ ∃ t, b * t = s) (hrb : ∀ s : A, b * s = 0 ↔ ∃ t, a * t = s) :
    IsGorensteinProjective A (ModuleCat.of A (Submodule.span A {b})) := by
  have hab : a * b = 0 := (hlb a).2 ⟨1, one_mul a⟩
  have hba : b * a = 0 := (hla b).2 ⟨1, one_mul b⟩
  have hg : ((alternatingMulRightComplex a b hab hba).sc' (-1) 0 1).g =
      ModuleCat.ofHom (LinearMap.toSpanSingleton A A a) :=
    (alternatingMulRightComplex_d hab hba (zero_add 1)).trans (by simp)
  have hker : LinearMap.ker (LinearMap.toSpanSingleton A A a) = Submodule.span A {b} := by
    ext r
    simp [Submodule.mem_span_singleton, hla]
  have hker' : LinearMap.ker ((alternatingMulRightComplex a b hab hba).sc' (-1) 0 1).g.hom =
      Submodule.span A {b} :=
    (congrArg (fun f ↦ LinearMap.ker f.hom) hg).trans hker
  exact ⟨_, isTotallyAcyclic_alternatingMulRightComplex hla hlb hra hrb,
    ⟨(alternatingMulRightComplex a b hab hba).cyclesIsoSc' (-1) 0 1 (by simp) (by simp) ≪≫
      ((alternatingMulRightComplex a b hab hba).sc' (-1) 0 1).moduleCatCyclesIso ≪≫
        (LinearEquiv.ofEq _ _ hker').toModuleIso⟩⟩

end ExactPair

end TauCeti
