/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Basic
public import TauCeti.CategoryTheory.Functor.ProZero
public import TauCeti.RingTheory.Almost.RootSetup
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Almost-pro-zero diagrams and almost-pro-isomorphisms

Let `S = (V, m)` be a basic setup and `C` a `V`-linear category, for instance `ModuleCat V`. A
diagram `F : J ⥤ C` is *almost-pro-zero* if every `ε ∈ m` kills, for every `j`, some map
`F.map f : F i ⟶ F j` of the diagram. For a tower `M₀ ← M₁ ← ⋯` of modules and the root setup of
a compatible system of `p`-power roots `t^{1/p^k}` of an element `t`, this says that for every `k`
and every `n` there is `n' ≥ n` such that `t^{1/p^k}` kills the image of the transition
`M_{n'} → M_n` (Bhatt, Definition 3.2). The index `n'` may depend on `k`: an almost-pro-zero tower
need not be the zero pro-object of almost modules, which would ask one `n'` to serve every `k`.

Being almost-pro-zero is weaker than being pro-zero (`CategoryTheory.Functor.IsProZero`), with
which it agrees for the classical setup `m = V`. Over a cofiltered index category, idempotence of
`m` makes almost-pro-zero diagrams a Serre class of the functor category, so the
*almost-pro-isomorphisms*, the morphisms of diagrams with almost-pro-zero kernel and cokernel,
are stable under composition and satisfy two-out-of-three. These are the error terms of Bhatt's
quantitative Riemann extension theorem, which compares a perfectoid ring modulo `tᵐ` with the
tower of its bounded functions on the rational annuli `{|tⁿ| ≤ |g|}`.

## Main declarations

* `TauCeti.Almost.BasicSetup.IsAlmostProZero`: almost-pro-zero diagrams.
* `TauCeti.Almost.BasicSetup.isAlmostProZero_iff_forall_proIsomorphisms_kernel_ι`: a diagram is
  almost-pro-zero iff, for every `ε ∈ m`, the inclusion of the kernel of `ε • 𝟙 F` (the subtower
  of `ε`-torsion) is a pro-isomorphism.
* `TauCeti.Almost.BasicSetup.ofCompatibleRoots_isAlmostProZero_iff` and
  `TauCeti.Almost.BasicSetup.ofCompatibleRoots_isAlmostProZero_iff_transitionOfLE`: for the root
  setup it suffices to test the roots, elementwise on the transitions of a tower.
* `TauCeti.Almost.BasicSetup.isAlmostProZero_of_isProZero` and
  `TauCeti.Almost.BasicSetup.isAlmostProZero_classical_iff`: pro-zero diagrams are almost-pro-zero,
  and conversely for the classical setup.
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
  ∀ ε ∈ S.ideal, ∀ j, ∃ (i : J) (f : i ⟶ j), ε • F.map f = 0

variable {S}

theorem isAlmostProZero_iff (F : J ⥤ C) :
    S.IsAlmostProZero F ↔ ∀ ε ∈ S.ideal, ∀ j, ∃ (i : J) (f : i ⟶ j), ε • F.map f = 0 :=
  Iff.rfl

/-- A diagram indexed by the opposite of a preorder is almost-pro-zero exactly when every
`ε ∈ m` kills, for every `i`, the transition into `F i` from some later term. -/
theorem isAlmostProZero_iff_forall_exists_le {ι : Type u₃} [Preorder ι] (F : ιᵒᵖ ⥤ C) :
    S.IsAlmostProZero F ↔
      ∀ ε ∈ S.ideal, ∀ i, ∃ (j : ι) (h : i ≤ j), ε • F.map (homOfLE h).op = 0 := by
  refine ⟨fun hF ε hε i ↦ ?_, fun hF ε hε i ↦ ?_⟩
  · obtain ⟨j, f, hf⟩ := hF ε hε (Opposite.op i)
    exact ⟨j.unop, leOfHom f.unop, by rwa [Subsingleton.elim (homOfLE _).op f]⟩
  · obtain ⟨j, h, hj⟩ := hF ε hε i.unop
    exact ⟨Opposite.op j, (homOfLE h).op, hj⟩

/-- Almost-pro-zero diagrams for a larger ideal are almost-pro-zero for a smaller one. -/
theorem IsAlmostProZero.mono {T : BasicSetup V} {F : J ⥤ C} (hF : T.IsAlmostProZero F)
    (hST : S.ideal ≤ T.ideal) : S.IsAlmostProZero F :=
  fun ε hε ↦ hF ε (hST hε)

/-- A pro-zero diagram is almost-pro-zero for every basic setup. -/
theorem isAlmostProZero_of_isProZero {F : J ⥤ C} (hF : F.IsProZero) : S.IsAlmostProZero F :=
  fun _ _ j ↦
    have ⟨i, f, hf⟩ := (Functor.isProZero_iff F).mp hF j
    ⟨i, f, by rw [hf, smul_zero]⟩

/-- For the classical setup `m = V`, almost-pro-zero means pro-zero. -/
@[simp]
theorem isAlmostProZero_classical_iff {F : J ⥤ C} :
    (classical V).IsAlmostProZero F ↔ F.IsProZero := by
  refine ⟨fun hF ↦ (Functor.isProZero_iff F).mpr fun j ↦ ?_, isAlmostProZero_of_isProZero⟩
  obtain ⟨i, f, hf⟩ := hF 1 (by simp [classical_ideal]) j
  exact ⟨i, f, by rwa [one_smul] at hf⟩

section RootSetup

variable {p : ℕ} (hp : 2 ≤ p) {ϖ : ℕ → V} (hϖ : ∀ n, ϖ (n + 1) ^ p = ϖ n)

/-- For the root setup of a compatible system of `p`-power roots `ϖ`, a diagram is almost-pro-zero
iff every root `ϖ k` kills, for every `j`, some map of the diagram into `F j`. -/
theorem ofCompatibleRoots_isAlmostProZero_iff (F : J ⥤ C) :
    (ofCompatibleRoots hp hϖ).IsAlmostProZero F ↔
      ∀ k j, ∃ (i : J) (f : i ⟶ j), ϖ k • F.map f = 0 := by
  refine ⟨fun hF k ↦ hF _ (root_mem_ofCompatibleRoots_ideal hp hϖ k), fun hF ε hε j ↦ ?_⟩
  obtain ⟨k, c, rfl⟩ := (mem_ofCompatibleRoots_ideal hp hϖ).mp hε
  obtain ⟨i, f, hf⟩ := hF k j
  exact ⟨i, f, by rw [mul_comm, mul_smul, hf, smul_zero]⟩

/-- **Bhatt's condition.** A tower of modules is almost-pro-zero for the root setup of `ϖ` iff
for all `k` and `n` there is `n' ≥ n` such that `ϖ k` kills the image of the transition
`M_{n'} → M_n`. -/
theorem ofCompatibleRoots_isAlmostProZero_iff_transitionOfLE (F : ModuleTower.{v} V) :
    (ofCompatibleRoots hp hϖ).IsAlmostProZero F ↔
      ∀ k n, ∃ (n' : ℕ) (h : n ≤ n'), ∀ x, ϖ k • F.transitionOfLE h x = 0 := by
  rw [ofCompatibleRoots_isAlmostProZero_iff]
  refine forall_congr' fun k ↦ ⟨fun hF n ↦ ?_, fun hF n ↦ ?_⟩
  · obtain ⟨n', f, hf⟩ := hF (Opposite.op n)
    exact ⟨n'.unop, leOfHom f.unop, fun x ↦ by simpa using congr(ModuleCat.Hom.hom $hf x)⟩
  · obtain ⟨n', h, hn'⟩ := hF n.unop
    exact ⟨Opposite.op n', (homOfLE h).op, by ext x; simpa using hn' x⟩

end RootSetup

/-- A diagram of almost zero modules is almost-pro-zero, whatever its transition maps. -/
theorem isAlmostProZero_of_forall_isAlmostZero {F : J ⥤ ModuleCat.{v} V}
    (hF : ∀ j, S.IsAlmostZero (F.obj j)) : S.IsAlmostProZero F :=
  fun ε hε j ↦ ⟨j, 𝟙 j, by ext x; simp [(hF j).smul_eq_zero hε]⟩

/-- Over a nonempty index category, a constant diagram is almost-pro-zero iff its value is almost
zero. -/
@[simp]
theorem isAlmostProZero_const_iff [Nonempty J] {M : ModuleCat.{v} V} :
    S.IsAlmostProZero ((Functor.const J).obj M) ↔ S.IsAlmostZero M := by
  refine ⟨fun hF ↦ isAlmostZero_iff.mpr fun ε hε x ↦ ?_, fun hM ↦
    isAlmostProZero_of_forall_isAlmostZero fun _ ↦ hM⟩
  obtain ⟨i, f, hf⟩ := hF ε hε (Classical.arbitrary J)
  simpa using congr(ModuleCat.Hom.hom $hf x)

/-- In a cofiltered diagram, the elements of `V` that kill some map of the diagram into `F j` are
closed under addition. -/
private theorem exists_add_smul_map_eq_zero [IsCofilteredOrEmpty J] {F : J ⥤ C} {j : J}
    {ε δ : V} (hε : ∃ (i : J) (f : i ⟶ j), ε • F.map f = 0)
    (hδ : ∃ (i : J) (f : i ⟶ j), δ • F.map f = 0) :
    ∃ (i : J) (f : i ⟶ j), (ε + δ) • F.map f = 0 := by
  obtain ⟨i₁, f₁, h₁⟩ := hε
  obtain ⟨i₂, f₂, h₂⟩ := hδ
  obtain ⟨k, g₁, g₂, hg⟩ := IsCofiltered.cospan f₁ f₂
  refine ⟨k, g₁ ≫ f₁, ?_⟩
  rw [add_smul]
  nth_rw 2 [hg]
  simp only [F.map_comp, ← Linear.comp_smul, h₁, h₂, comp_zero, add_zero]

/-- **Cofinal reindexing.** For an initial functor `G : I ⥤ J` out of a cofiltered category, a
diagram `F : J ⥤ C` is almost-pro-zero exactly when `G ⋙ F` is. -/
theorem isAlmostProZero_comp_iff {I : Type u₃} [Category.{v₃} I] [IsCofilteredOrEmpty I]
    (G : I ⥤ J) [G.Initial] (F : J ⥤ C) :
    S.IsAlmostProZero (G ⋙ F) ↔ S.IsAlmostProZero F := by
  have hG := ((Functor.initial_iff_of_isCofiltered G).1 inferInstance).1
  refine ⟨fun hF ε hε j ↦ ?_, fun hF ε hε i ↦ ?_⟩
  · obtain ⟨c, ⟨u⟩⟩ := hG j
    obtain ⟨i, g, hg⟩ := hF ε hε c
    refine ⟨G.obj i, G.map g ≫ u, ?_⟩
    rw [F.map_comp, ← Linear.smul_comp, ← Functor.comp_map, hg, zero_comp]
  · -- Kill `F (G i)` by `ε` along some `f : j ⟶ G i`, reach `j` from some `G c`, and compare the
    -- resulting map `G c ⟶ G i` with a map in the image of `G` over a common lower bound.
    obtain ⟨j, f, hf⟩ := hF ε hε (G.obj i)
    obtain ⟨c, ⟨u⟩⟩ := hG j
    obtain ⟨c', t, ht⟩ := Functor.Initial.exists_eq G
      (G.map (IsCofiltered.minToLeft c i) ≫ u ≫ f) (G.map (IsCofiltered.minToRight c i))
    refine ⟨c', t ≫ IsCofiltered.minToRight c i, ?_⟩
    rw [Functor.comp_map, G.map_comp, ← ht]
    simp only [Functor.map_comp, ← Linear.comp_smul, hf, comp_zero]

/-- **Cofinal monotone reindexing of inverse systems.** If `φ : ι → κ` is monotone and cofinal and
`ι` is directed, then an inverse system `F` indexed by `κ` is almost-pro-zero exactly when its
reindexing along `φ` is. -/
theorem isAlmostProZero_monotone_comp_iff {ι : Type u₃} {κ : Type u₄} [Preorder ι]
    [IsDirectedOrder ι] [Preorder κ] {φ : ι → κ} (hφ : Monotone φ) (hcof : ∀ k, ∃ i, k ≤ φ i)
    (F : κᵒᵖ ⥤ C) : S.IsAlmostProZero (hφ.functor.op ⋙ F) ↔ S.IsAlmostProZero F :=
  have := (hφ.final_functor_iff).2 hcof
  isAlmostProZero_comp_iff _ F

end Preadditive

section Abelian

variable (C : Type u₂) [Category.{v₂} C] [Abelian C] [Linear V C]

variable {S C} in
/-- **Torsion subdiagrams.** A diagram `F` in a `V`-linear abelian category is almost-pro-zero iff
for every `ε ∈ m` the inclusion of the kernel of `ε • 𝟙 F`, the subdiagram of `ε`-torsion, is a
pro-isomorphism (Bhatt, Definition 3.2). -/
theorem isAlmostProZero_iff_forall_proIsomorphisms_kernel_ι (F : J ⥤ C) :
    S.IsAlmostProZero F ↔
      ∀ ε ∈ S.ideal, Functor.proIsomorphisms J C (kernel.ι (ε • 𝟙 F)) := by
  simp only [Functor.proIsomorphisms_kernel_ι_smul_id_iff, isAlmostProZero_iff]

variable (J) [IsCofilteredOrEmpty J]

/-- Over a cofiltered index category, almost-pro-zero diagrams form a Serre class of the functor
category: they contain zero and are closed under subobjects, quotients and extensions. -/
instance isSerreClass_isAlmostProZero :
    ObjectProperty.IsSerreClass (S.IsAlmostProZero (J := J) (C := C)) where
  exists_zero := ⟨0, isZero_zero _, isAlmostProZero_of_isProZero (Functor.isProZero_zero)⟩
  prop_of_mono {X Y} f _ hY ε hε j := by
    obtain ⟨i, g, hg⟩ := hY ε hε j
    refine ⟨i, g, (cancel_mono (f.app j)).1 ?_⟩
    rw [Linear.smul_comp, f.naturality, ← Linear.comp_smul, hg]
    simp
  prop_of_epi {X Y} f _ hX ε hε j := by
    obtain ⟨i, g, hg⟩ := hX ε hε j
    refine ⟨i, g, (cancel_epi (f.app i)).1 ?_⟩
    rw [Linear.comp_smul, ← f.naturality, ← Linear.smul_comp, hg]
    simp
  prop_X₂_of_shortExact {T} hT h₁ h₃ ε hε := by
    -- Since `m * m = m`, it suffices to treat products `a * b` with `a, b ∈ m`, and sums, which
    -- the cofiltered index category handles.
    refine S.mul_induction_on (p := fun ε ↦ ∀ j, ∃ (i : J) (f : i ⟶ j), ε • T.X₂.map f = 0) hε
      (fun a ha b hb j ↦ ?_) fun _ _ hx hy j ↦ exists_add_smul_map_eq_zero (hx j) (hy j)
    -- Let `b` kill `T.X₁.map α` for some `α : i ⟶ j` and `a` kill `T.X₃.map β` for some
    -- `β : k ⟶ i`. Then `a • T.X₂.map β` factors through `T.X₁ i` by exactness at `i`, and
    -- `(a * b) • T.X₂.map (β ≫ α)` factors through `b • T.X₁.map α = 0`.
    obtain ⟨i, α, hα⟩ := h₁ b hb j
    obtain ⟨k, β, hβ⟩ := h₃ a ha i
    have hTi := hT.map_of_exact ((evaluation J C).obj i)
    have := hTi.mono_f
    have hk : (a • T.X₂.map β) ≫ T.g.app i = 0 := by
      rw [Linear.smul_comp, T.g.naturality, ← Linear.comp_smul, hβ, comp_zero]
    refine ⟨k, β ≫ α, ?_⟩
    rw [T.X₂.map_comp, mul_smul, ← Linear.comp_smul, ← Linear.smul_comp,
      ← hTi.exact.lift_f _ hk]
    dsimp
    rw [Category.assoc, Linear.comp_smul, ← T.f.naturality, ← Linear.smul_comp, hα]
    simp

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
