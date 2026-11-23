/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Functor.ProZero
public import TauCeti.RingTheory.Almost.RootSetup

/-!
# Almost-pro-zero diagrams and almost-pro-isomorphisms

Let `S = (V, m)` be a basic setup and `C` a `V`-linear category, for instance `ModuleCat V`. A
diagram `F : J ⥤ C` is *almost-pro-zero* if every `ε ∈ m` kills, for every `j`, some map
`F.map f : F i ⟶ F j` of the diagram, that is, `F` is pro-`ε`-torsion
(`CategoryTheory.Functor.IsProTorsionBy`). For a tower `M₀ ← M₁ ← ⋯` of modules and the root
setup of a compatible system of `p`-power roots `t^{1/p^k}` of an element `t`, this says that for
every `k` and every `n` there is `n' ≥ n` such that `t^{1/p^k}` kills the image of the transition
`M_{n'} → M_n` (Bhatt, Definition 3.2). The index `n'` may depend on `k`: an almost-pro-zero tower
need not be the zero pro-object of almost modules, which would ask one `n'` to serve every `k`.

Being almost-pro-zero is weaker than being pro-zero (`CategoryTheory.Functor.IsProZero`), with
which it agrees when `m = V`, for instance for the classical setup or when `t` is a unit. Over a
cofiltered index category, idempotence of `m` makes almost-pro-zero diagrams a Serre class of the
functor category, so the *almost-pro-isomorphisms*, the morphisms of diagrams with almost-pro-zero
kernel and cokernel, are stable under composition and satisfy two-out-of-three. These are the error
terms of Bhatt's quantitative Riemann extension theorem, which compares a perfectoid ring modulo
`tᵐ` with the tower of its bounded functions on the rational annuli `{|tⁿ| ≤ |g|}`.

## Main declarations

* `TauCeti.Almost.BasicSetup.IsAlmostProZero`: almost-pro-zero diagrams, that is, pro-`ε`-torsion
  ones for every `ε ∈ m` (`TauCeti.Almost.BasicSetup.isAlmostProZero_iff_forall_isProTorsionBy`).
* `TauCeti.Almost.BasicSetup.isAlmostProZero_iff_forall_proIsomorphisms_kernel_ι`: a diagram is
  almost-pro-zero iff, for every `ε ∈ m`, the inclusion of the kernel of `ε • 𝟙 F` (the subtower
  of `ε`-torsion) is a pro-isomorphism.
* `TauCeti.Almost.BasicSetup.ofCompatibleRoots_isAlmostProZero_iff` and
  `TauCeti.Almost.BasicSetup.ofCompatibleRoots_isAlmostProZero_iff_transitionOfLE`: for the root
  setup it suffices to test the roots, elementwise on the transitions of a tower.
* `TauCeti.Almost.BasicSetup.isAlmostProZero_of_isProZero` and
  `TauCeti.Almost.BasicSetup.isAlmostProZero_iff_isProZero_of_ideal_eq_top`: pro-zero diagrams are
  almost-pro-zero, and conversely when `m = V`, for instance for the classical setup
  (`TauCeti.Almost.BasicSetup.isAlmostProZero_classical_iff`) or for the root setup of a unit
  (`TauCeti.Almost.BasicSetup.ofCompatibleRoots_isAlmostProZero_iff_isProZero`); for the zero setup
  every diagram is almost-pro-zero (`TauCeti.Almost.BasicSetup.isAlmostProZero_zero`).
* `TauCeti.Almost.BasicSetup.isAlmostProZero_of_forall_isAlmostZero` and
  `TauCeti.Almost.BasicSetup.isAlmostProZero_const_iff`: diagrams of almost zero modules are
  almost-pro-zero, and a constant diagram is almost-pro-zero iff its value is almost zero.
* `TauCeti.Almost.BasicSetup.isAlmostProZero_comp_iff` and
  `TauCeti.Almost.BasicSetup.isAlmostProZero_monotone_comp_iff`: invariance under cofinal
  reindexing.
* `TauCeti.Almost.BasicSetup.isSerreClass_isAlmostProZero`: almost-pro-zero diagrams over a
  cofiltered index category form a Serre class.
* `TauCeti.Almost.BasicSetup.almostProIsomorphisms`: the almost-pro-isomorphisms, which contain the
  pro-isomorphisms (`TauCeti.Almost.BasicSetup.proIsomorphisms_le_almostProIsomorphisms`).

## References

* B. Bhatt, *On the direct summand conjecture and its derived variant*, Invent. Math. 212 (2018),
  §3, Definition 3.2 and Example 3.3.
* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.1.
-/

public section

namespace TauCeti.Almost.BasicSetup

open CategoryTheory Limits ZeroObject

universe v u u₁ v₁ u₂ v₂ u₃ v₃ u₄

variable {V : Type u} [CommRing V] (S : BasicSetup V) {J : Type u₁} [Category.{v₁} J]

section Preadditive

variable {C : Type u₂} [Category.{v₂} C] [Preadditive C] [Linear V C]

/-- A diagram `F : J ⥤ C` in a `V`-linear category is *almost-pro-zero* for the basic setup `S` if
every `ε` in the ideal `m` kills, for every `j`, some map `F.map f : F i ⟶ F j` of the diagram. For
a tower of modules and the root setup of `t^{1/p^∞}`, this is Bhatt's condition that for all `k`
and `n` some transition `M_{n'} → M_n` has image killed by `t^{1/p^k}`
(`ofCompatibleRoots_isAlmostProZero_iff_transitionOfLE`). -/
def IsAlmostProZero (F : J ⥤ C) : Prop :=
  ∀ ε ∈ S.ideal, F.IsProTorsionBy ε

variable {S}

/-- A diagram is almost-pro-zero exactly when it is pro-`ε`-torsion for every `ε ∈ m`. -/
theorem isAlmostProZero_iff_forall_isProTorsionBy (F : J ⥤ C) :
    S.IsAlmostProZero F ↔ ∀ ε ∈ S.ideal, F.IsProTorsionBy ε :=
  Iff.rfl

theorem isAlmostProZero_iff (F : J ⥤ C) :
    S.IsAlmostProZero F ↔ ∀ ε ∈ S.ideal, ∀ j, ∃ (i : J) (f : i ⟶ j), ε • F.map f = 0 :=
  forall₂_congr fun ε _ ↦ F.isProTorsionBy_iff ε

/-- A diagram indexed by the opposite of a preorder is almost-pro-zero exactly when every
`ε ∈ m` kills, for every `i`, the transition into `F i` from some later term. -/
theorem isAlmostProZero_iff_forall_exists_le {ι : Type u₃} [Preorder ι] (F : ιᵒᵖ ⥤ C) :
    S.IsAlmostProZero F ↔
      ∀ ε ∈ S.ideal, ∀ i, ∃ (j : ι) (h : i ≤ j), ε • F.map (homOfLE h).op = 0 :=
  forall₂_congr fun ε _ ↦ F.isProTorsionBy_iff_forall_exists_le ε

/-- Almost-pro-zero diagrams for a larger ideal are almost-pro-zero for a smaller one. -/
theorem IsAlmostProZero.mono {T : BasicSetup V} {F : J ⥤ C} (hF : T.IsAlmostProZero F)
    (hST : S.ideal ≤ T.ideal) : S.IsAlmostProZero F :=
  fun ε hε ↦ hF ε (hST hε)

/-- A pro-zero diagram is almost-pro-zero for every basic setup. -/
theorem isAlmostProZero_of_isProZero {F : J ⥤ C} (hF : F.IsProZero) : S.IsAlmostProZero F :=
  fun ε _ ↦ hF.isProTorsionBy ε

/-- If `m = V`, almost-pro-zero means pro-zero. -/
theorem isAlmostProZero_iff_isProZero_of_ideal_eq_top (h : S.ideal = ⊤) {F : J ⥤ C} :
    S.IsAlmostProZero F ↔ F.IsProZero :=
  ⟨fun hF ↦ Functor.isProTorsionBy_one_iff.mp
    ((isAlmostProZero_iff_forall_isProTorsionBy F).mp hF 1 (h ▸ Submodule.mem_top)),
    isAlmostProZero_of_isProZero⟩

/-- For the classical setup `m = V`, almost-pro-zero means pro-zero. -/
@[simp]
theorem isAlmostProZero_classical_iff {F : J ⥤ C} :
    (classical V).IsAlmostProZero F ↔ F.IsProZero :=
  isAlmostProZero_iff_isProZero_of_ideal_eq_top classical_ideal

/-- For the zero setup `m = 0`, every diagram is almost-pro-zero. -/
@[simp]
theorem isAlmostProZero_zero (F : J ⥤ C) : (zero V).IsAlmostProZero F :=
  (isAlmostProZero_iff_forall_isProTorsionBy F).mpr fun ε hε ↦ by
    rw [zero_ideal, Ideal.mem_bot] at hε
    exact hε ▸ F.isProTorsionBy_zero

section RootSetup

variable {p : ℕ} (hp : 2 ≤ p) {ϖ : ℕ → V} (hϖ : ∀ n, ϖ (n + 1) ^ p = ϖ n)

/-- For the root setup of a compatible system of `p`-power roots `ϖ`, a diagram is almost-pro-zero
iff every root `ϖ k` kills, for every `j`, some map of the diagram into `F j`. -/
theorem ofCompatibleRoots_isAlmostProZero_iff (F : J ⥤ C) :
    (ofCompatibleRoots hp hϖ).IsAlmostProZero F ↔
      ∀ k j, ∃ (i : J) (f : i ⟶ j), ϖ k • F.map f = 0 := by
  refine ⟨fun hF k ↦ (F.isProTorsionBy_iff _).mp (hF _ (root_mem_ofCompatibleRoots_ideal hp hϖ k)),
    fun hF ε hε ↦ ?_⟩
  obtain ⟨k, c, rfl⟩ := (mem_ofCompatibleRoots_ideal hp hϖ).mp hε
  exact ((F.isProTorsionBy_iff _).mpr (hF k)).mul_right c

/-- **Bhatt's condition.** A tower of modules is almost-pro-zero for the root setup of `ϖ` iff
for all `k` and `n` there is `n' ≥ n` such that `ϖ k` kills the image of the transition
`M_{n'} → M_n`. -/
theorem ofCompatibleRoots_isAlmostProZero_iff_transitionOfLE (F : ModuleTower.{v} V) :
    (ofCompatibleRoots hp hϖ).IsAlmostProZero F ↔
      ∀ k n, ∃ (n' : ℕ) (h : n ≤ n'), ∀ x, ϖ k • F.transitionOfLE h x = 0 := by
  rw [ofCompatibleRoots_isAlmostProZero_iff]
  refine forall_congr' fun k ↦
    ((F.isProTorsionBy_iff (ϖ k)).symm.trans (F.isProTorsionBy_iff_forall_exists_le (ϖ k))).trans ?_
  simp only [ModuleCat.hom_ext_iff, ModuleCat.hom_smul, ModuleCat.hom_zero, LinearMap.ext_iff,
    LinearMap.smul_apply, LinearMap.zero_apply, ModuleTower.transitionOfLE_def]

/-- For the root setup of `ϖ`, if `ϖ 0` is a unit then almost-pro-zero means pro-zero. -/
theorem ofCompatibleRoots_isAlmostProZero_iff_isProZero (ht : IsUnit (ϖ 0)) (F : J ⥤ C) :
    (ofCompatibleRoots hp hϖ).IsAlmostProZero F ↔ F.IsProZero :=
  isAlmostProZero_iff_isProZero_of_ideal_eq_top
    (Ideal.eq_top_of_isUnit_mem _ (root_mem_ofCompatibleRoots_ideal hp hϖ 0) ht)

end RootSetup

/-- A diagram of almost zero modules is almost-pro-zero, whatever its transition maps. -/
theorem isAlmostProZero_of_forall_isAlmostZero {F : J ⥤ ModuleCat.{v} V}
    (hF : ∀ j, S.IsAlmostZero (F.obj j)) : S.IsAlmostProZero F :=
  (isAlmostProZero_iff F).mpr fun ε hε j ↦ ⟨j, 𝟙 j, by ext x; simp [(hF j).smul_eq_zero hε]⟩

/-- Over a nonempty index category, a constant diagram is almost-pro-zero iff its value is almost
zero. -/
@[simp]
theorem isAlmostProZero_const_iff [Nonempty J] {M : ModuleCat.{v} V} :
    S.IsAlmostProZero ((Functor.const J).obj M) ↔ S.IsAlmostZero M := by
  refine ⟨fun hF ↦ isAlmostZero_iff.mpr fun ε hε x ↦ ?_, fun hM ↦
    isAlmostProZero_of_forall_isAlmostZero fun _ ↦ hM⟩
  obtain ⟨i, f, hf⟩ := (isAlmostProZero_iff _).mp hF ε hε (Classical.arbitrary J)
  simpa using congr(ModuleCat.Hom.hom $hf x)

/-- **Cofinal reindexing.** For an initial functor `G : I ⥤ J` out of a cofiltered category, a
diagram `F : J ⥤ C` is almost-pro-zero exactly when `G ⋙ F` is. -/
theorem isAlmostProZero_comp_iff {I : Type u₃} [Category.{v₃} I] [IsCofilteredOrEmpty I]
    (G : I ⥤ J) [G.Initial] (F : J ⥤ C) :
    S.IsAlmostProZero (G ⋙ F) ↔ S.IsAlmostProZero F :=
  forall₂_congr fun ε _ ↦ Functor.isProTorsionBy_comp_iff G F ε

/-- **Cofinal monotone reindexing of inverse systems.** If `φ : ι → κ` is monotone and cofinal and
`ι` is directed, then an inverse system `F` indexed by `κ` is almost-pro-zero exactly when its
reindexing along `φ` is. -/
theorem isAlmostProZero_monotone_comp_iff {ι : Type u₃} {κ : Type u₄} [Preorder ι]
    [IsDirectedOrder ι] [Preorder κ] {φ : ι → κ} (hφ : Monotone φ) (hcof : ∀ k, ∃ i, k ≤ φ i)
    (F : κᵒᵖ ⥤ C) : S.IsAlmostProZero (hφ.functor.op ⋙ F) ↔ S.IsAlmostProZero F :=
  forall₂_congr fun ε _ ↦ Functor.isProTorsionBy_monotone_comp_iff hφ hcof F ε

end Preadditive

section Abelian

variable (C : Type u₂) [Category.{v₂} C] [Abelian C] [Linear V C]

variable {S C} in
/-- **Torsion subdiagrams.** A diagram `F` in a `V`-linear abelian category is almost-pro-zero iff
for every `ε ∈ m` the inclusion of the kernel of `ε • 𝟙 F`, the subdiagram of `ε`-torsion, is a
pro-isomorphism (Bhatt, Definition 3.2). -/
theorem isAlmostProZero_iff_forall_proIsomorphisms_kernel_ι (F : J ⥤ C) :
    S.IsAlmostProZero F ↔
      ∀ ε ∈ S.ideal, Functor.proIsomorphisms J C (kernel.ι (ε • 𝟙 F)) :=
  forall₂_congr fun ε _ ↦ (Functor.proIsomorphisms_kernel_ι_smul_id_iff ε F).symm

variable (J) [IsCofilteredOrEmpty J]

/-- Over a cofiltered index category, almost-pro-zero diagrams form a Serre class of the functor
category: they contain zero and are closed under subobjects, quotients and extensions. -/
instance isSerreClass_isAlmostProZero :
    ObjectProperty.IsSerreClass (S.IsAlmostProZero (J := J) (C := C)) where
  exists_zero := ⟨0, isZero_zero _, isAlmostProZero_of_isProZero (Functor.isProZero_zero)⟩
  prop_of_mono f _ hY := (isAlmostProZero_iff_forall_isProTorsionBy _).mpr fun ε hε ↦
    ((isAlmostProZero_iff_forall_isProTorsionBy _).mp hY ε hε).of_mono f
  prop_of_epi f _ hX := (isAlmostProZero_iff_forall_isProTorsionBy _).mpr fun ε hε ↦
    ((isAlmostProZero_iff_forall_isProTorsionBy _).mp hX ε hε).of_epi f
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    rw [isAlmostProZero_iff_forall_isProTorsionBy] at h₁ h₃ ⊢
    -- Since `m * m = m`, it suffices to treat products `a * b` with `a, b ∈ m`, and sums, which
    -- the cofiltered index category handles.
    exact fun ε hε ↦ S.mul_induction_on (p := T.X₂.IsProTorsionBy) hε
      (fun a ha b hb ↦ (h₁ b hb).of_shortExact hT (h₃ a ha)) fun _ _ hx hy ↦ hx.add hy

/-- The *almost-pro-isomorphisms* of diagrams `J ⥤ C` over a cofiltered index category: the
morphisms whose kernel and cokernel are almost-pro-zero (`almostProIsomorphisms_iff`). This is
Mathlib's class `ObjectProperty.isoModSerre` of isomorphisms modulo the Serre class of
almost-pro-zero diagrams, so almost-pro-isomorphisms are stable under composition and retracts and
satisfy two-out-of-three. -/
abbrev almostProIsomorphisms : MorphismProperty (J ⥤ C) :=
  ObjectProperty.isoModSerre (S.IsAlmostProZero (J := J) (C := C))

variable {S J C}

theorem almostProIsomorphisms_iff {F G : J ⥤ C} (f : F ⟶ G) :
    S.almostProIsomorphisms J C f ↔
      S.IsAlmostProZero (kernel f) ∧ S.IsAlmostProZero (cokernel f) :=
  Iff.rfl

example : (S.almostProIsomorphisms J C).IsMultiplicative := inferInstance

example : (S.almostProIsomorphisms J C).HasTwoOutOfThreeProperty := inferInstance

/-- Every pro-isomorphism is an almost-pro-isomorphism. -/
theorem proIsomorphisms_le_almostProIsomorphisms :
    Functor.proIsomorphisms J C ≤ S.almostProIsomorphisms J C :=
  fun _ _ _ hf ↦ ⟨isAlmostProZero_of_isProZero hf.1, isAlmostProZero_of_isProZero hf.2⟩

end Abelian

end TauCeti.Almost.BasicSetup
