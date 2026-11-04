/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Noetherian.Basic

import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Coherent modules and coherent rings

An `R`-module `M` is *coherent* (`Module.IsCoherent R M`) if it is finitely generated and every
finitely generated submodule of `M` is finitely presented. A ring `R` is *(left) coherent*
(`TauCeti.IsCoherentRing R`) if it is coherent as a left module over itself, i.e. every finitely
generated left ideal of `R` is finitely presented.

Coherence is the minimal finiteness condition under which finitely presented modules behave like
finitely generated modules over a Noetherian ring without requiring ascending chains of arbitrary
submodules to stabilize. Over any ring, coherent modules form a full subcategory closed under
kernels, cokernels, images, extensions (the two-out-of-three property in short exact sequences),
finite direct sums, and sums and intersections of coherent submodules inside a coherent ambient
module. Over a coherent ring, a module is coherent if and only if it is finitely presented. Over a
commutative ring, `M ⊗[R] N` and `M →ₗ[R] N` are coherent as soon as `M` is finitely presented and
`N` is coherent (in particular whenever both `M` and `N` are coherent). Coherence is also preserved
by localization and by quotients modulo finitely generated ideals.

This algebra underpins coherent module theory over non-Noetherian rings such as polynomial rings in
infinitely many variables (`TauCeti.RingTheory.Coherent.MvPolynomial`) and algebras topologically of
finite presentation over non-discrete rank-one valuation rings.

## Main definitions

* `Module.IsCoherent R M`: `M` is finitely generated and every finitely generated submodule of `M`
  is finitely presented.
* `TauCeti.IsCoherentRing R`: `R` is coherent as a module over itself.

## Main results

* `Module.IsCoherent.toFinitePresentation`: every coherent module is finitely presented.
* `Module.isCoherent_iff_forall_fg_ker`: `M` is coherent iff `M` is finitely generated and every
  linear map `(Fin n → R) →ₗ[R] M` has finitely generated kernel.
* `Submodule.isCoherent_iff_fg`: a submodule of a coherent module is coherent iff it is finitely
  generated.
* `Module.IsCoherent.of_exact_left`, `Module.IsCoherent.of_exact_right`,
  `Module.IsCoherent.of_exact_middle`: the two-out-of-three property in short exact sequences.
* `Module.IsCoherent.ker`, `Module.IsCoherent.coker`, `Module.IsCoherent.range`,
  `Module.IsCoherent.sup`, `Module.IsCoherent.inf`, `Module.IsCoherent.prod`,
  `Module.IsCoherent.pi`: abelian and finite-product closure properties of coherent modules.
* `TauCeti.IsCoherentRing.isCoherent_iff_finitePresentation`: over a coherent ring, a module is
  coherent iff it is finitely presented.
* `Module.FinitePresentation.of_restrictScalars_finitePresentation`,
  `Module.finitePresentation_iff_of_finitePresentation`: ascent and comparison of finite
  presentation along module-finite and finitely presented ring extensions.
* `Module.IsCoherent.tensorProduct`, `Module.IsCoherent.linearMap`: over a commutative ring, if `M`
  is finitely presented and `N` is coherent, then `M ⊗[R] N` and `M →ₗ[R] N` are coherent.
* `Module.isCoherent_iff_of_surjective`, `Ideal.Quotient.isCoherent_iff`,
  `TauCeti.IsCoherentRing.quotient`: scalar restriction along a surjective finitely presented
  algebra and coherence of quotients by finitely generated ideals.
* `Module.IsCoherent.of_isLocalizedModule`, `TauCeti.IsCoherentRing.of_isLocalization`:
  localization preserves coherent modules and coherent commutative rings.
* `IsNoetherianRing.isCoherentRing`, `Module.isCoherent_iff_finite`: Noetherian rings are coherent,
  and over them coherence coincides with finite generation.

## References

* N. Bourbaki, *Algèbre Commutative*, Ch. I, §2, Exercise 12.
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique I*, Ch. 0, 5.3.1–5.3.4.
* S. Bosch and W. Lütkebohmert, *Formal and rigid geometry. I. Rigid spaces*,
  Math. Ann. 295 (1993), §1, p. 294.
* [The Stacks Project, Section 10.90, Tags 05CU and 05CV](https://stacks.math.columbia.edu/tag/05CU).
-/

public section

open LinearMap TensorProduct

/-! ### Definition and equivalence invariance -/

section Semiring

namespace Module

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- An `R`-module `M` is *coherent* if it is finitely generated and every finitely generated
submodule of `M` is finitely presented (Stacks, Definition 10.90.1, Tag 05CU). -/
@[stacks 05CU]
class IsCoherent : Prop extends Module.Finite R M where
  /-- Every finitely generated submodule of a coherent module is finitely presented. -/
  finitePresentation_of_fg : ∀ ⦃N : Submodule R M⦄, N.FG → Module.FinitePresentation R N

theorem isCoherent_iff :
    Module.IsCoherent R M ↔
      Module.Finite R M ∧ ∀ ⦃N : Submodule R M⦄, N.FG → Module.FinitePresentation R N :=
  ⟨fun h ↦ ⟨h.toFinite, h.finitePresentation_of_fg⟩, fun ⟨_, h₂⟩ ↦ ⟨h₂⟩⟩

end Module

namespace TauCeti

/-- A (left) *coherent ring* is a semiring that is coherent as a left module over itself, i.e.
every finitely generated left ideal is finitely presented (Stacks, Definition 10.90.1, Tag 05CU). -/
@[stacks 05CU]
abbrev IsCoherentRing (R : Type*) [Semiring R] : Prop :=
  Module.IsCoherent R R

theorem isCoherentRing_iff {R : Type*} [Semiring R] :
    IsCoherentRing R ↔ Module.IsCoherent R R :=
  Iff.rfl

/-- A semiring is coherent if and only if every finitely generated left ideal is finitely
presented. -/
theorem isCoherentRing_iff_ideal_finitePresentation (R : Type*) [Semiring R] :
    IsCoherentRing R ↔ ∀ ⦃I : Ideal R⦄, I.FG → Module.FinitePresentation R I :=
  ⟨fun h _ hI ↦ h.finitePresentation_of_fg hI, fun h ↦ ⟨h⟩⟩

end TauCeti

end Semiring

/-! ### Basic properties over a ring -/

section Ring

variable {R M N P : Type*} [Ring R]
  [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

namespace Module.IsCoherent

/-- Every coherent module is finitely presented. -/
instance (priority := 100) toFinitePresentation [h : Module.IsCoherent R M] :
    Module.FinitePresentation R M := by
  have : Module.FinitePresentation R (⊤ : Submodule R M) :=
    h.finitePresentation_of_fg Module.Finite.fg_top
  exact .of_equiv Submodule.topEquiv

/-- Coherence is preserved along `R`-linear equivalences. -/
theorem of_equiv [h : Module.IsCoherent R M] (e : M ≃ₗ[R] N) : Module.IsCoherent R N := by
  have : Module.Finite R N := Module.Finite.equiv e
  refine ⟨fun K hK ↦ ?_⟩
  have hK' : (K.comap e.toLinearMap).FG := by
    rw [Submodule.comap_equiv_eq_map_symm]
    exact hK.map e.symm.toLinearMap
  have : Module.FinitePresentation R ↥(K.comap e.toLinearMap) := h.finitePresentation_of_fg hK'
  let eK : ↥(K.comap e.toLinearMap) ≃ₗ[R] K :=
    e.submoduleMap (K.comap e.toLinearMap) ≪≫ₗ
      LinearEquiv.ofEq _ _ (Submodule.map_comap_eq_of_surjective e.surjective K)
  exact .of_equiv eK

variable (R M) in
instance (priority := 900) of_subsingleton [Subsingleton M] : Module.IsCoherent R M where
  finitePresentation_of_fg _ _ := inferInstance

/-- Every finitely generated submodule of a coherent module is itself coherent. -/
theorem of_fg_submodule [h : Module.IsCoherent R M] {K : Submodule R M} (hK : K.FG) :
    Module.IsCoherent R K := by
  have : Module.Finite R K := Module.Finite.iff_fg.mpr hK
  refine ⟨fun L hL ↦ ?_⟩
  have : Module.FinitePresentation R ↥(L.map K.subtype) :=
    h.finitePresentation_of_fg (hL.map K.subtype)
  exact .of_equiv (Submodule.equivMapOfInjective K.subtype K.injective_subtype L).symm

/-- A finitely generated module that embeds `R`-linearly into a coherent module is coherent. -/
theorem of_injective [Module.Finite R M] [Module.IsCoherent R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f) : Module.IsCoherent R M := by
  have : Module.IsCoherent R (LinearMap.range f) := of_fg_submodule (Submodule.fg_range f)
  exact of_equiv (LinearEquiv.ofInjective f hf).symm

/-- The image of a finitely generated module in a coherent module is coherent. -/
instance range [Module.Finite R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (LinearMap.range f) :=
  of_fg_submodule (Submodule.fg_range f)

end Module.IsCoherent

theorem LinearEquiv.isCoherent_iff (e : M ≃ₗ[R] N) :
    Module.IsCoherent R M ↔ Module.IsCoherent R N :=
  ⟨fun _ ↦ .of_equiv e, fun _ ↦ .of_equiv e.symm⟩

/-- A submodule of a coherent module is coherent if and only if it is finitely generated. -/
theorem Submodule.isCoherent_iff_fg [Module.IsCoherent R M] {K : Submodule R M} :
    Module.IsCoherent R K ↔ K.FG :=
  ⟨fun _ ↦ Module.Finite.iff_fg.mp inferInstance, Module.IsCoherent.of_fg_submodule⟩

/-- A module `M` is coherent if and only if it is finitely generated and every linear map from a
finite free module `(Fin n → R)` into `M` has finitely generated kernel
(Bourbaki, *Algèbre Commutative*, Ch. I, §2, Exercise 12; Stacks, Lemma 10.90.2, Tag 05CU). -/
@[stacks 05CU]
theorem Module.isCoherent_iff_forall_fg_ker :
    Module.IsCoherent R M ↔
      Module.Finite R M ∧ ∀ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), (LinearMap.ker f).FG := by
  refine ⟨fun h ↦ ⟨h.toFinite, fun n f ↦ ?_⟩, fun ⟨hfin, hker⟩ ↦ ⟨fun N hN ↦ ?_⟩⟩
  · have : Module.FinitePresentation R (LinearMap.range f) :=
      h.finitePresentation_of_fg (Submodule.fg_range f)
    have hfg := Module.FinitePresentation.fg_ker f.rangeRestrict f.surjective_rangeRestrict
    rwa [LinearMap.ker_rangeRestrict] at hfg
  · -- Present `N` by a finite coordinate map and restrict its kernel from `M`.
    have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
    obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin' R N
    refine Module.finitePresentation_of_free_of_surjective p hp ?_
    have hkeq : LinearMap.ker (N.subtype ∘ₗ p) = LinearMap.ker p := by
      rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr N.injective_subtype, Submodule.comap_bot]
    exact hkeq ▸ hker m (N.subtype ∘ₗ p)

/-! ### Short exact sequences and abelian closure -/

namespace Module.IsCoherent

/-- In a left-exact sequence `0 → M →[f] N →[g] P`, if `N` and `P` are coherent, then `M` is
coherent (Stacks, Lemma 10.90.3(1), Tag 05CU). Surjectivity of `g` is not needed. -/
@[stacks 05CU]
theorem of_exact_left [Module.IsCoherent R N] [hP : Module.IsCoherent R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f) (hfg : Function.Exact f g) :
    Module.IsCoherent R M := by
  have : Module.FinitePresentation R (LinearMap.range g) :=
    hP.finitePresentation_of_fg (Submodule.fg_range g)
  have hker : (LinearMap.ker g).FG := by
    rw [← LinearMap.ker_rangeRestrict g]
    exact Module.FinitePresentation.fg_ker g.rangeRestrict g.surjective_rangeRestrict
  have hrf : (LinearMap.range f).FG := LinearMap.exact_iff.mp hfg ▸ hker
  have : Module.Finite R (LinearMap.range f) := Module.Finite.iff_fg.mpr hrf
  have : Module.Finite R M := Module.Finite.equiv (LinearEquiv.ofInjective f hf).symm
  exact of_injective f hf

/-- Variant of `Module.IsCoherent.of_exact_left` for a short exact sequence
`0 → M →[f] N →[g] P → 0`: when `g` is surjective, `P` need only be finitely presented. -/
theorem of_exact_left_of_surjective [Module.IsCoherent R N] [Module.FinitePresentation R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) : Module.IsCoherent R M := by
  have hrf : (LinearMap.range f).FG :=
    LinearMap.exact_iff.mp hfg ▸ Module.FinitePresentation.fg_ker g hg
  have : Module.Finite R (LinearMap.range f) := Module.Finite.iff_fg.mpr hrf
  have : Module.Finite R M := Module.Finite.equiv (LinearEquiv.ofInjective f hf).symm
  exact of_injective f hf

/-- In a right-exact sequence `M →[f] N →[g] P → 0`, if `M` is finitely generated (in particular
if `M` is coherent) and `N` is coherent, then `P` is coherent
(Stacks, Lemma 10.90.3(2), Tag 05CU). Injectivity of `f` is not needed. -/
@[stacks 05CU]
theorem of_exact_right [Module.Finite R M] [hN : Module.IsCoherent R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.IsCoherent R P := by
  have : Module.Finite R P := Module.Finite.of_surjective g hg
  refine ⟨fun K hK ↦ ?_⟩
  -- Pull `K ≤ P` back to `L = g⁻¹(K) ≤ N`; both `g(L) = K` and `L ∩ ker g = range f` are f.g.
  set L : Submodule R N := K.comap g
  have hLmap : L.map g = K := Submodule.map_comap_eq_of_surjective hg K
  have hker_le : LinearMap.ker g ≤ L := fun x hx ↦ by
    simp only [L, Submodule.mem_comap, LinearMap.mem_ker.mp hx, zero_mem]
  have hL : L.FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker g (hLmap ▸ hK) ?_
    rw [inf_of_le_right hker_le, LinearMap.exact_iff.mp hfg]
    exact Submodule.fg_range f
  have : Module.FinitePresentation R L := hN.finitePresentation_of_fg hL
  -- Restrict `g` to a surjection `L → K` whose kernel maps isomorphically onto `ker g = range f`.
  let gL : L →ₗ[R] K := g.restrict fun _ hx ↦ hx
  have hgL : Function.Surjective gL := fun ⟨y, hy⟩ ↦ by
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker_gL : (LinearMap.ker gL).map L.subtype = LinearMap.ker g := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype]
    exact ⟨fun ⟨⟨z, _⟩, hz, hzx⟩ ↦ hzx ▸ congrArg Subtype.val hz,
      fun hx ↦ ⟨⟨x, hker_le hx⟩, Subtype.ext hx, rfl⟩⟩
  have hfg_ker : (LinearMap.ker gL).FG := by
    refine Submodule.fg_of_fg_map_injective L.subtype L.injective_subtype ?_
    rw [hker_gL, LinearMap.exact_iff.mp hfg]
    exact Submodule.fg_range f
  exact Module.finitePresentation_of_surjective gL hgL hfg_ker

/-- In a short exact sequence `0 → M →[f] N →[g] P → 0`, if `M` and `P` are coherent, then `N` is
coherent (Stacks, Lemma 10.90.3(3), Tag 05CU). -/
@[stacks 05CU]
theorem of_exact_middle [hM : Module.IsCoherent R M] [hP : Module.IsCoherent R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) : Module.IsCoherent R N := by
  have hker_eq : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp hfg
  have : Module.FinitePresentation R (LinearMap.ker g) := by
    rw [hker_eq]
    exact .of_equiv (LinearEquiv.ofInjective f hf)
  have : Module.FinitePresentation R N := Module.finitePresentation_of_ker g hg
  refine ⟨fun K hK ↦ ?_⟩
  -- For f.g. `K ≤ N`, `g(K) ≤ P` is f.p., so the kernel `K ∩ ker g` of `K → g(K)` is f.g.
  have : Module.Finite R K := Module.Finite.iff_fg.mpr hK
  have : Module.FinitePresentation R ↥(K.map g) := hP.finitePresentation_of_fg (hK.map g)
  let gK : K →ₗ[R] ↥(K.map g) :=
    (g.comp K.subtype).codRestrict (K.map g) fun x ↦ Submodule.mem_map_of_mem x.2
  have hgK : Function.Surjective gK := fun ⟨_, x, hx, rfl⟩ ↦ ⟨⟨x, hx⟩, rfl⟩
  have hfg_ker : (LinearMap.ker gK).FG := Module.FinitePresentation.fg_ker gK hgK
  -- Pull `ker gK ⊆ range f` back to `M` along the injection `f`; coherence of `M` makes it f.p.
  set L : Submodule R M := ((LinearMap.ker gK).map K.subtype).comap f
  have hsub : (LinearMap.ker gK).map K.subtype ≤ LinearMap.range f := by
    rintro _ ⟨⟨x, hx⟩, hxk, rfl⟩
    rw [← hker_eq, LinearMap.mem_ker]
    exact congrArg Subtype.val (LinearMap.mem_ker.mp hxk)
  have hLf : L.map f = (LinearMap.ker gK).map K.subtype :=
    Submodule.map_comap_eq_self hsub
  have hLfg : L.FG :=
    Submodule.fg_of_fg_map_injective f hf (hLf.symm ▸ hfg_ker.map K.subtype)
  have : Module.FinitePresentation R L := hM.finitePresentation_of_fg hLfg
  let eL : L ≃ₗ[R] LinearMap.ker gK :=
    Submodule.equivMapOfInjective f hf L ≪≫ₗ
      LinearEquiv.ofEq _ _ hLf ≪≫ₗ
      (Submodule.equivMapOfInjective K.subtype K.injective_subtype (LinearMap.ker gK)).symm
  have : Module.FinitePresentation R (LinearMap.ker gK) := .of_equiv eL
  exact Module.finitePresentation_of_ker gK hgK

/-- The kernel of a linear map between coherent modules is coherent
(Stacks, Lemma 10.90.4, Tag 05CU). -/
instance ker [Module.IsCoherent R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (LinearMap.ker f) :=
  of_exact_left (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
    f.exact_subtype_ker_map

/-- The quotient of a coherent module by a finitely generated submodule is coherent. -/
instance quotient [Module.IsCoherent R N] (K : Submodule R N) [Module.Finite R K] :
    Module.IsCoherent R (N ⧸ K) :=
  of_exact_right K.subtype K.mkQ K.mkQ_surjective
    (LinearMap.exact_iff.mpr (by rw [Submodule.ker_mkQ, Submodule.range_subtype]))

/-- The cokernel `N ⧸ LinearMap.range f` of a linear map from a finitely generated module (in
particular from a coherent module) to a coherent module is coherent
(Stacks, Lemma 10.90.4, Tag 05CU). -/
theorem coker [Module.Finite R M] [Module.IsCoherent R N] (f : M →ₗ[R] N) :
    Module.IsCoherent R (N ⧸ LinearMap.range f) :=
  inferInstance

/-- The sum of two coherent submodules of a coherent module is coherent
(Stacks, Lemma 10.90.4, Tag 05CU). -/
instance sup [Module.IsCoherent R M] (N₁ N₂ : Submodule R M)
    [Module.IsCoherent R N₁] [Module.IsCoherent R N₂] :
    Module.IsCoherent R ↥(N₁ ⊔ N₂) :=
  of_fg_submodule ((Submodule.isCoherent_iff_fg.mp ‹_›).sup (Submodule.isCoherent_iff_fg.mp ‹_›))

/-- Products of coherent modules are coherent. -/
instance prod [Module.IsCoherent R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M × N) :=
  of_exact_middle (.inl R M N) (.snd R M N) LinearMap.inl_injective LinearMap.snd_surjective
    Function.Exact.inl_snd

/-- Finite indexed products of coherent modules are coherent. -/
instance pi {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.IsCoherent R (M i)] :
    Module.IsCoherent R (∀ i, M i) := by
  refine Module.pi_induction' (motive := fun X _ _ ↦ Module.IsCoherent R X)
      (motive' := fun X _ _ ↦ Module.IsCoherent R X) R ?_ ?_ ?_ ?_ M inferInstance
  · exact fun e (_ : Module.IsCoherent R _) ↦ .of_equiv e
  · exact fun e (_ : Module.IsCoherent R _) ↦ .of_equiv e
  · infer_instance
  · introv h₁ h₂
    infer_instance

/-- Finite direct sums `ι →₀ M` of a coherent module are coherent. -/
instance finsupp {ι : Type*} [Finite ι] [Module.IsCoherent R M] :
    Module.IsCoherent R (ι →₀ M) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  exact .of_equiv (Finsupp.linearEquivFunOnFinite R M ι).symm

/-- The intersection of two coherent submodules of a coherent module is coherent
(Stacks, Lemma 10.90.4, Tag 05CU). -/
instance inf [Module.IsCoherent R M] (N₁ N₂ : Submodule R M)
    [Module.IsCoherent R N₁] [Module.IsCoherent R N₂] :
    Module.IsCoherent R ↥(N₁ ⊓ N₂) := by
  -- Realize `N₁ ⊓ N₂` as the kernel of `(x, y) ↦ x - y` from `N₁ × N₂` into `M`.
  let δ : N₁ × N₂ →ₗ[R] M :=
    N₁.subtype.comp (.fst R N₁ N₂) - N₂.subtype.comp (.snd R N₁ N₂)
  let ι : ↥(N₁ ⊓ N₂) →ₗ[R] N₁ × N₂ :=
    (Submodule.inclusion inf_le_left).prod (Submodule.inclusion inf_le_right)
  have hι : Function.Injective ι := fun x y hxy ↦
    Subtype.ext (congrArg (fun p : N₁ × N₂ ↦ (p.1 : M)) hxy)
  have hex : Function.Exact ι δ := fun ⟨x₁, x₂⟩ ↦ by
    simp only [δ, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, Submodule.coe_subtype, sub_eq_zero, Set.mem_range]
    exact ⟨fun h ↦ ⟨⟨x₁.1, x₁.2, h ▸ x₂.2⟩, Prod.ext rfl (Subtype.ext h)⟩,
      fun ⟨z, hz⟩ ↦ (congrArg (fun p : N₁ × N₂ ↦ (p.1 : M)) hz).symm.trans
        (congrArg (fun p : N₁ × N₂ ↦ (p.2 : M)) hz)⟩
  exact of_exact_left ι δ hι hex

end Module.IsCoherent

/-! ### Coherent rings and Noetherian compatibility -/

namespace TauCeti.IsCoherentRing

/-- Over a coherent ring, a module is coherent if and only if it is finitely presented
(Stacks, Lemma 10.90.5, Tag 05CU). -/
@[stacks 05CU]
theorem isCoherent_iff_finitePresentation [IsCoherentRing R] :
    Module.IsCoherent R M ↔ Module.FinitePresentation R M := by
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  exact Module.IsCoherent.of_exact_right g f hf hgf

/-- Every finitely presented module over a coherent ring is coherent. -/
theorem isCoherent_of_finitePresentation [IsCoherentRing R] [Module.FinitePresentation R M] :
    Module.IsCoherent R M :=
  isCoherent_iff_finitePresentation.mpr ‹_›

end TauCeti.IsCoherentRing

/-- A ring `R` is coherent if and only if every finitely presented `R`-module in the same universe
is coherent. -/
theorem TauCeti.isCoherentRing_iff_forall_finitePresentation.{u} {R : Type u} [Ring R] :
    TauCeti.IsCoherentRing R ↔
      ∀ (M : Type u) [AddCommGroup M] [Module R M],
        Module.FinitePresentation R M → Module.IsCoherent R M :=
  ⟨fun _ _ _ _ _ ↦ TauCeti.IsCoherentRing.isCoherent_of_finitePresentation,
    fun h ↦ h R inferInstance⟩

private theorem isCoherentRing_of_ringEquiv {R S : Type*} [Ring R] [Ring S]
    (e : R ≃+* S) [TauCeti.IsCoherentRing R] : TauCeti.IsCoherentRing S := by
  rw [TauCeti.isCoherentRing_iff, Module.isCoherent_iff_forall_fg_ker]
  refine ⟨inferInstance, fun n f ↦ ?_⟩
  have : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let Φ : (Fin n → R) →ₛₗ[e.toRingHom] (Fin n → S) :=
    { toFun := fun v i ↦ e (v i)
      map_add' := fun u v ↦ funext fun i ↦ e.map_add (u i) (v i)
      map_smul' := fun r v ↦ funext fun i ↦ e.map_mul r (v i) }
  let f' : (Fin n → R) →ₗ[R] R :=
    { toFun := fun v ↦ e.symm (f (Φ v))
      map_add' := fun u v ↦ by rw [map_add, map_add, map_add]
      map_smul' := fun r v ↦ by
        have her : e.symm (e.toRingHom r) = r := by simp
        rw [RingHom.id_apply, Φ.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, her, smul_eq_mul] }
  have hker := ((Module.isCoherent_iff_forall_fg_ker.mp
    (inferInstance : Module.IsCoherent R R)).2 n f').map Φ
  have heq : (LinearMap.ker f').map Φ = LinearMap.ker f := by
    ext w
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    refine ⟨fun ⟨v, hv, hvw⟩ ↦ ?_,
      fun hw ↦ ⟨fun i ↦ e.symm (w i), ?_, funext fun i ↦ e.apply_symm_apply (w i)⟩⟩
    · rw [← hvw]
      exact e.symm.injective (hv.trans (map_zero e.symm).symm)
    · have hΦ : Φ (fun i ↦ e.symm (w i)) = w := funext fun i ↦ e.apply_symm_apply (w i)
      simp only [f', LinearMap.coe_mk, AddHom.coe_mk]
      rw [hΦ, hw, map_zero]
  rwa [heq] at hker

/-- Every ring equivalence transports ring coherence. -/
theorem RingEquiv.isCoherentRing_iff {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) :
    TauCeti.IsCoherentRing R ↔ TauCeti.IsCoherentRing S :=
  ⟨fun _ ↦ isCoherentRing_of_ringEquiv e, fun _ ↦ isCoherentRing_of_ringEquiv e.symm⟩

/-- If `S` is finite as a left `R`-module and `P` is finitely presented as an `R`-module, then `P`
is finitely presented as an `S`-module (Stacks, Lemma 10.6.4, Tag 0519). -/
@[stacks 0519]
theorem Module.FinitePresentation.of_restrictScalars_finitePresentation
    (R S P : Type*) [Ring R] [Ring S] [AddCommGroup P] [Module R S] [IsScalarTower R S S]
    [Module R P] [Module S P] [IsScalarTower R S P]
    [Module.Finite R S] [Module.FinitePresentation R P] :
    Module.FinitePresentation S P := by
  have : Module.Finite S P := .of_restrictScalars_finite R S P
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S P
  refine Module.finitePresentation_of_surjective f hf ?_
  exact Submodule.FG.of_restrictScalars R
    (Module.FinitePresentation.fg_ker (f.restrictScalars R) hf)

/-- Every finitely generated module over a Noetherian ring is coherent. -/
theorem Module.isCoherent_of_finite [IsNoetherianRing R] [Module.Finite R M] :
    Module.IsCoherent R M where
  finitePresentation_of_fg N hN := by
    have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
    exact Module.finitePresentation_of_finite R N

/-- Over a Noetherian ring, a module is coherent if and only if it is finitely generated. -/
theorem Module.isCoherent_iff_finite [IsNoetherianRing R] :
    Module.IsCoherent R M ↔ Module.Finite R M :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ Module.isCoherent_of_finite⟩

/-- Every Noetherian ring is coherent. -/
instance IsNoetherianRing.isCoherentRing [IsNoetherianRing R] : TauCeti.IsCoherentRing R :=
  Module.isCoherent_of_finite

end Ring

/-! ### Commutative ring operations: `⊗`, `Hom`, annihilators, quotients and localization -/

section CommRing

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace Module.IsCoherent

/-- Over a commutative ring, if `M` is finitely presented and `N` is coherent (in particular when
both `M` and `N` are coherent), `M ⊗[R] N` is coherent. -/
instance tensorProduct [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M ⊗[R] N) := by
  -- Tensor a finite presentation of `M` with `N` to get a presentation by finite products of `N`.
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let ePi (k : ℕ) : ((Fin k → R) ⊗[R] N) ≃ₗ[R] (Fin k → N) :=
    TensorProduct.comm R (Fin k → R) N ≪≫ₗ TensorProduct.piScalarRight R R N (Fin k)
  have : Module.Finite R ((Fin m → R) ⊗[R] N) := Module.Finite.equiv (ePi m).symm
  have : Module.IsCoherent R ((Fin n → R) ⊗[R] N) := .of_equiv (ePi n).symm
  exact of_exact_right (g.rTensor N) (f.rTensor N) (LinearMap.rTensor_surjective N hf)
    (rTensor_exact N hgf hf)

/-- Symmetrical version of `Module.IsCoherent.tensorProduct` when `M` is coherent and `N` is
finitely presented. -/
theorem tensorProduct_of_left [Module.IsCoherent R M] [Module.FinitePresentation R N] :
    Module.IsCoherent R (M ⊗[R] N) :=
  .of_equiv (TensorProduct.comm R N M)

/-- Over a commutative ring, if `M` is finitely presented and `N` is coherent (in particular when
both `M` and `N` are coherent), `M →ₗ[R] N` is coherent. -/
instance linearMap [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M →ₗ[R] N) := by
  -- Apply `Hom_R(-, N)` to a finite presentation of `M` to realize `M →ₗ[R] N` as a kernel.
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let ePair (k : ℕ) : ((Fin k → R) →ₗ[R] N) ≃ₗ[R] (Fin k → N) :=
    (LinearMap.lsum R (fun _ : Fin k ↦ R) R).symm ≪≫ₗ
      LinearEquiv.piCongrRight fun _ ↦ LinearMap.ringLmapEquivSelf R R N
  have : Module.IsCoherent R ((Fin n → R) →ₗ[R] N) := .of_equiv (ePair n).symm
  have : Module.IsCoherent R ((Fin m → R) →ₗ[R] N) := .of_equiv (ePair m).symm
  exact of_exact_left (f.lcomp R N) (g.lcomp R N)
    (lcomp_injective_of_surjective f hf) (exact_lcomp_of_exact_of_surjective N hgf hf)

/-- The `a`-torsion submodule `M[a]` of a coherent module over a commutative ring is coherent. -/
instance torsionBy [Module.IsCoherent R M] (a : R) :
    Module.IsCoherent R (Submodule.torsionBy R M a) := by
  have heq : Submodule.torsionBy R M a = LinearMap.ker (LinearMap.lsmul R M a) := rfl
  rw [heq]
  infer_instance

/-- For a coherent module `M` and a finitely generated ideal `I`, the submodule of elements of `M`
killed by `I` is coherent (Bosch–Lütkebohmert I, §1, Lemma 1.4(c)). -/
theorem torsionBySet_of_fg [Module.IsCoherent R M] {I : Ideal R} (hI : I.FG) :
    Module.IsCoherent R (Submodule.torsionBySet R M I) := by
  obtain ⟨s, hs⟩ := hI
  let ev : M →ₗ[R] (s → M) := LinearMap.pi fun r ↦ LinearMap.lsmul R M (r : R)
  have hker : Submodule.torsionBySet R M I = LinearMap.ker ev := by
    ext x
    simp only [Submodule.mem_torsionBySet_iff, ev, LinearMap.mem_ker, LinearMap.pi_apply,
      funext_iff, Pi.zero_apply, LinearMap.lsmul_apply]
    refine ⟨fun h r ↦ h ⟨r.1, hs ▸ Submodule.subset_span r.2⟩, fun h ⟨a, ha⟩ ↦ ?_⟩
    dsimp only
    rw [← hs] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · exact fun b hb ↦ h ⟨b, hb⟩
    · exact zero_smul R x
    · intro b c _ _ hb hc
      rw [add_smul, hb, hc, add_zero]
    · intro r b _ hb
      rw [smul_eq_mul, mul_smul, hb, smul_zero]
  rw [hker]
  infer_instance

end Module.IsCoherent

/-- Over a coherent commutative ring, the annihilator ideal `Ann_R(M)` of any finitely generated
coherent module `M` is coherent (Bosch–Lütkebohmert I, §1, Lemma 1.4(c)). -/
theorem TauCeti.IsCoherentRing.annihilator [TauCeti.IsCoherentRing R] [Module.IsCoherent R M] :
    Module.IsCoherent R ↥(Module.annihilator R M) := by
  obtain ⟨s, hs⟩ := ‹Module.IsCoherent R M›.toFinite
  let ev : R →ₗ[R] (s → M) := LinearMap.pi fun m ↦ LinearMap.toSpanSingleton R M (m : M)
  have hker : Module.annihilator R M = LinearMap.ker ev := by
    ext r
    simp only [Module.mem_annihilator, ev, LinearMap.mem_ker, LinearMap.pi_apply, funext_iff,
      Pi.zero_apply, LinearMap.toSpanSingleton_apply]
    refine ⟨fun h m ↦ h m.1, fun h x ↦ ?_⟩
    have hx : x ∈ Submodule.span R (s : Set M) := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · exact fun m hm ↦ h ⟨m, hm⟩
    · exact smul_zero r
    · intro y z _ _ hy hz
      rw [smul_add, hy, hz, add_zero]
    · intro a y _ hy
      rw [smul_comm, hy, smul_zero]
  rw [hker]
  infer_instance

section SurjectiveAlgebra

variable {P : Type*} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

/-- Over an `R`-algebra `S` that is finitely presented as an `R`-module, an `S`-module `P` is
finitely presented over `S` if and only if it is finitely presented over `R`
(Stacks, Lemma 10.6.4, Tag 0519). -/
@[stacks 0519]
theorem Module.finitePresentation_iff_of_finitePresentation [Module.FinitePresentation R S] :
    Module.FinitePresentation S P ↔ Module.FinitePresentation R P :=
  ⟨fun _ ↦ .trans R P S, fun _ ↦ .of_restrictScalars_finitePresentation R S P⟩

/-- Along a surjective `R`-algebra `S` that is finitely presented as an `R`-module, an `S`-module
`P` is coherent over `S` if and only if it is coherent over `R`
(Stacks, Lemma 10.90.6, Tag 05CU). -/
@[stacks 05CU]
theorem Module.isCoherent_iff_of_surjective
    (hsurj : Function.Surjective (algebraMap R S)) [Module.FinitePresentation R S] :
    Module.IsCoherent S P ↔ Module.IsCoherent R P := by
  constructor
  · intro hS
    have : Module.Finite R P := Module.Finite.trans S P
    refine ⟨fun K hK ↦ ?_⟩
    -- Promote `K : Submodule R P` to an `S`-submodule using surjectivity of `R → S`.
    let KS : Submodule S P :=
      { carrier := K
        add_mem' := K.add_mem
        zero_mem' := K.zero_mem
        smul_mem' := fun s x hx ↦ by
          obtain ⟨r, rfl⟩ := hsurj s
          rw [IsScalarTower.algebraMap_smul S r x]
          exact K.smul_mem r hx }
    have hKS_fg : KS.FG := Submodule.FG.of_restrictScalars R hK
    have : Module.FinitePresentation S KS := hS.finitePresentation_of_fg hKS_fg
    exact .trans R KS S
  · intro hR
    have : Module.Finite S P := Module.Finite.of_restrictScalars_finite R S P
    refine ⟨fun K hK ↦ ?_⟩
    have hKR_fg : (K.restrictScalars R).FG := hK.restrictScalars_of_surjective hsurj
    have : Module.FinitePresentation R (K.restrictScalars R) :=
      hR.finitePresentation_of_fg hKR_fg
    have : Module.FinitePresentation R K :=
      .of_equiv ((K.restrictScalarsEquiv R).restrictScalars R)
    exact .of_restrictScalars_finitePresentation R S K

end SurjectiveAlgebra

/-- For a finitely generated ideal `I` of `R`, an `(R ⧸ I)`-module `P` is coherent over `R ⧸ I` if
and only if it is coherent over `R` (Stacks, Lemma 10.90.6, Tag 05CU). -/
@[stacks 05CU]
theorem Ideal.Quotient.isCoherent_iff {I : Ideal R} (hI : I.FG)
    {P : Type*} [AddCommGroup P] [Module R P] [Module (R ⧸ I) P] [IsScalarTower R (R ⧸ I) P] :
    Module.IsCoherent (R ⧸ I) P ↔ Module.IsCoherent R P := by
  have : Module.FinitePresentation R (R ⧸ I) :=
    Module.finitePresentation_of_surjective I.mkQ I.mkQ_surjective (by rwa [Submodule.ker_mkQ])
  exact Module.isCoherent_iff_of_surjective Ideal.Quotient.mk_surjective

/-- The quotient of a coherent commutative ring by a finitely generated ideal is a coherent ring
(Stacks, Lemma 10.90.5, Tag 05CU). -/
@[stacks 05CU]
theorem TauCeti.IsCoherentRing.quotient [TauCeti.IsCoherentRing R] {I : Ideal R} (hI : I.FG) :
    TauCeti.IsCoherentRing (R ⧸ I) := by
  rw [TauCeti.isCoherentRing_iff, Ideal.Quotient.isCoherent_iff hI,
    TauCeti.IsCoherentRing.isCoherent_iff_finitePresentation]
  exact Module.finitePresentation_of_surjective I.mkQ I.mkQ_surjective (by rwa [Submodule.ker_mkQ])

/-! ### Localization of coherent modules and rings -/

section Localization

variable (T : Submonoid R) {Rₜ Mₜ : Type*} [CommRing Rₜ] [Algebra R Rₜ]
  [AddCommGroup Mₜ] [Module R Mₜ] [Module Rₜ Mₜ] [IsScalarTower R Rₜ Mₜ]

/-- Localization preserves coherent modules (Stacks, Lemma 10.90.7, Tag 05CV). -/
@[stacks 05CV]
theorem Module.IsCoherent.of_isLocalizedModule [IsLocalization T Rₜ] [hM : Module.IsCoherent R M]
    (f : M →ₗ[R] Mₜ) [IsLocalizedModule T f] : Module.IsCoherent Rₜ Mₜ := by
  have hbc : IsBaseChange Rₜ f := (isLocalizedModule_iff_isBaseChange T Rₜ f).mp inferInstance
  have : Module.Finite Rₜ Mₜ := Module.Finite.equiv hbc.equiv
  refine ⟨fun K hK ↦ ?_⟩
  classical
  obtain ⟨s, hs⟩ := hK
  -- Clear denominators on the finite generating set `s` of `K ≤ Mₜ` to obtain `L ≤ M` f.g.
  choose p hp using fun y : s ↦ IsLocalizedModule.mk'_surjective T f y.1
  dsimp only [Function.uncurry] at hp
  let L : Submodule R M := Submodule.span R (Set.range fun y : s ↦ (p y).1)
  have hLfg : L.FG := ⟨Finset.univ.image fun y : s ↦ (p y).1, by simp [L]⟩
  have : Module.FinitePresentation R L := hM.finitePresentation_of_fg hLfg
  have hLK : L.localized' Rₜ T f = K := by
    refine le_antisymm ?_ ?_
    · dsimp only [L]
      rw [Submodule.localized'_span, Submodule.span_le]
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      rw [← IsLocalizedModule.mk'_cancel' f (p y).1 (p y).2, hp y, Submonoid.smul_def,
        ← IsScalarTower.algebraMap_smul Rₜ]
      exact K.smul_mem _ (hs ▸ Submodule.subset_span y.2)
    · rw [← hs, Submodule.span_le]
      exact fun y hy ↦ ⟨(p ⟨y, hy⟩).1, Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩, (p ⟨y, hy⟩).2,
        hp ⟨y, hy⟩⟩
  have : Module.FinitePresentation Rₜ ↥(L.localized' Rₜ T f) :=
    FinitePresentation.of_isBaseChange (L.toLocalized' Rₜ T f)
      ((isLocalizedModule_iff_isBaseChange T Rₜ (L.toLocalized' Rₜ T f)).mp inferInstance)
  exact .of_equiv (LinearEquiv.ofEq _ _ hLK)

instance Module.IsCoherent.localizedModule [Module.IsCoherent R M] :
    Module.IsCoherent (Localization T) (LocalizedModule T M) :=
  .of_isLocalizedModule T (LocalizedModule.mkLinearMap T M)

/-- Localization of a coherent commutative ring is a coherent ring
(Stacks, Lemma 10.90.7, Tag 05CV). -/
@[stacks 05CV]
theorem TauCeti.IsCoherentRing.of_isLocalization [IsLocalization T Rₜ]
    [TauCeti.IsCoherentRing R] : TauCeti.IsCoherentRing Rₜ :=
  Module.IsCoherent.of_isLocalizedModule T (Algebra.linearMap R Rₜ)

instance TauCeti.IsCoherentRing.localization [TauCeti.IsCoherentRing R] :
    TauCeti.IsCoherentRing (Localization T) :=
  TauCeti.IsCoherentRing.of_isLocalization T

end Localization

end CommRing
