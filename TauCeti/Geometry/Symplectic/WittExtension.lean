/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.Basic
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic
public import TauCeti.Geometry.Symplectic.SymplecticTransport
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Witt's extension theorem for symplectic vector spaces

Let `(V, ω₁)` and `(W, ω₂)` be finite-dimensional real symplectic vector spaces of the same
dimension, `S` a subspace of `V` and `f : S → W` an injective linear map preserving the
restricted forms, `ω₂ (f x) (f y) = ω₁ x y`. **Witt's extension theorem** says that `f` is the
restriction of a linear symplectomorphism `e : V ≃ₗ[ℝ] W`
(`TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`). The subspace `S` is arbitrary: it may
be isotropic, symplectic, or degenerate of any rank. The case `S = 0` is the linear Darboux
theorem, that any two symplectic vector spaces of the same dimension are symplectomorphic
(`TauCeti.SymplecticForm.exists_isSymplectomorphism`).

The proof extends `f` one vector at a time, as a partial linear map `V →ₗ.[ℝ] W`, until its domain
is all of `V`. Write `T` for the image of `f`. Given `v ∉ S`, a vector `v' ∉ T` with
`ω₂ (f s) v' = ω₁ s v` for all `s ∈ S` lets `f` extend to `S ⊕ ℝ v` by `v ↦ v'`, injectively and
isometrically. Such a pair exists for a suitable `v`:

* if `S` is coisotropic, `S^ω ≤ S`, any `v ∉ S` works: nondegeneracy of `ω₂` gives a `v'` with the
  prescribed pairings, and `v' = f s₀` would put `v - s₀` in `S^ω ≤ S`;
* otherwise pick `v ∈ S^ω` outside `S`, and `v' ∈ T^ω` outside `T`. Such a `v'` exists because `T`
  is not coisotropic either: `f` carries the radical `S ∩ S^ω` onto the radical `T ∩ T^ω`, and
  `S^ω`, `T^ω` have the same dimension, so `S^ω ≤ S` exactly when `T^ω ≤ T`.

## Main results

* `TauCeti.SymplecticForm.exists_isSymplectomorphism_extend`: an injective linear map from a
  subspace preserving the forms extends to a symplectomorphism.
* `TauCeti.SymplecticForm.exists_isSymplectomorphism_extend_linearEquiv`: the same for a linear
  isomorphism between two subspaces.
* `TauCeti.SymplecticForm.exists_isSymplectomorphism`: two symplectic vector spaces of the same
  finite dimension are symplectomorphic.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 2.1 (linear symplectic geometry).
* E. Artin, *Geometric Algebra*, Interscience, 1957, Chapter III, Theorem 3.9 (Witt's theorem).
-/

public section

namespace TauCeti

namespace SymplecticForm

open Module

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W}

/-- Through an injective linear map `f` into a finite-dimensional symplectic space, every linear
functional on the source is paired against some vector: `ω₂ (f u) w = φ u`. -/
private lemma exists_apply_eq_of_injective [FiniteDimensional ℝ W] (ω₂ : SymplecticForm W)
    {U : Type*} [AddCommGroup U] [Module ℝ U] (f : U →ₗ[ℝ] W) (hf : Function.Injective f)
    (φ : U →ₗ[ℝ] ℝ) : ∃ w, ∀ u, ω₂ (f u) w = φ u := by
  obtain ⟨h, hh⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
  refine ⟨-(ω₂.toBilinForm.toDual ω₂.nondegenerate).symm (φ ∘ₗ h), fun u => ?_⟩
  simp only [map_neg, ω₂.neg_eq, LinearMap.BilinForm.apply_toDual_symm_apply,
    LinearMap.comp_apply, ← LinearMap.comp_apply h f, hh, LinearMap.id_apply]

section PartialIsometry

variable (g : V →ₗ.[ℝ] W)

/-- An injective form-preserving partial map carries the radical `S ∩ S^ω` of its domain onto the
radical `T ∩ T^ω` of its image. -/
private lemma map_radical_eq (hiso : ∀ x y : g.domain, ω₂ (g x) (g y) = ω₁ x y) :
    ((g.domain ⊓ ω₁.orthogonal g.domain).comap g.domain.subtype).map g.toFun =
      LinearMap.range g.toFun ⊓ ω₂.orthogonal (LinearMap.range g.toFun) := by
  ext w
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf,
    LinearMap.mem_range, LinearPMap.toFun_eq_coe]
  constructor
  · rintro ⟨s, ⟨-, hs⟩, rfl⟩
    refine ⟨⟨s, rfl⟩, mem_orthogonal_iff.2 ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [LinearPMap.toFun_eq_coe, hiso]
    exact mem_orthogonal_iff.1 hs t t.2
  · rintro ⟨⟨s, rfl⟩, hw⟩
    refine ⟨s, ⟨s.2, mem_orthogonal_iff.2 fun y hy => ?_⟩, rfl⟩
    rw [← hiso ⟨y, hy⟩ s]
    exact mem_orthogonal_iff.1 hw _ (LinearMap.mem_range_self g.toFun _)

/-- If an injective form-preserving partial map between symplectic spaces of the same finite
dimension has coisotropic image, its domain is coisotropic. -/
private lemma orthogonal_domain_le [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hdim : finrank ℝ V = finrank ℝ W) (hinj : Function.Injective g)
    (hiso : ∀ x y : g.domain, ω₂ (g x) (g y) = ω₁ x y)
    (hT : ω₂.orthogonal (LinearMap.range g.toFun) ≤ LinearMap.range g.toFun) :
    ω₁.orthogonal g.domain ≤ g.domain := by
  set S := g.domain
  set T := LinearMap.range g.toFun
  set R := (S ⊓ ω₁.orthogonal S).comap S.subtype
  have hR : finrank ℝ R = finrank ℝ ↥(S ⊓ ω₁.orthogonal S) :=
    (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
  have hRT : finrank ℝ R = finrank ℝ ↥(T ⊓ ω₂.orthogonal T) := by
    rw [← map_radical_eq g hiso]
    exact (R.equivMapOfInjective g.toFun hinj).finrank_eq
  have hST : finrank ℝ S = finrank ℝ T := (LinearEquiv.ofInjective g.toFun hinj).finrank_eq
  have hS := ω₁.finrank_orthogonal S
  have hTo := ω₂.finrank_orthogonal T
  rw [inf_eq_right.2 hT] at hRT
  exact inf_eq_right.1 <| Submodule.eq_of_le_of_finrank_eq inf_le_right (by omega)

/-- A partial isometry whose domain is not everything admits a vector `v` outside the domain
`S` and a vector `v'` outside the image `T` with `ω₂ (g s) v' = ω₁ s v` for all `s ∈ S`. -/
private lemma exists_extension_pair [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hdim : finrank ℝ V = finrank ℝ W) (hinj : Function.Injective g)
    (hiso : ∀ x y : g.domain, ω₂ (g x) (g y) = ω₁ x y) (htop : g.domain ≠ ⊤) :
    ∃ v ∉ g.domain, ∃ v' ∉ LinearMap.range g.toFun, ∀ s : g.domain, ω₂ (g s) v' = ω₁ s v := by
  by_cases hco : ω₁.orthogonal g.domain ≤ g.domain
  · obtain ⟨v, hv⟩ : ∃ v, v ∉ g.domain := by
      by_contra! h
      exact htop (eq_top_iff.2 fun x _ => h x)
    obtain ⟨v', hv'⟩ := exists_apply_eq_of_injective ω₂ g.toFun hinj
      (ω₁.toBilinForm.flip v ∘ₗ g.domain.subtype)
    refine ⟨v, hv, v', ?_, hv'⟩
    rintro ⟨s₀, hs₀⟩
    apply hv
    have hmem : v - s₀ ∈ ω₁.orthogonal g.domain := mem_orthogonal_iff.2 fun y hy => by
      have h₁ : ω₂ (g ⟨y, hy⟩) v' = ω₁ y v := by simpa using hv' ⟨y, hy⟩
      have h₂ : ω₂ (g ⟨y, hy⟩) v' = ω₁ y s₀ := by
        rw [← hs₀, LinearPMap.toFun_eq_coe, hiso]
      simp only [map_sub]
      exact sub_eq_zero.2 (h₁.symm.trans h₂)
    simpa using add_mem (hco hmem) s₀.2
  · obtain ⟨v, hv, hvS⟩ := IsConcreteLE.not_le_iff_exists.1 hco
    obtain ⟨v', hv', hv'T⟩ := IsConcreteLE.not_le_iff_exists.1
      (mt (orthogonal_domain_le g hdim hinj hiso) hco)
    exact ⟨v, hvS, v', hv'T, fun s => (mem_orthogonal_iff.1 hv' _
      (LinearMap.mem_range_self g.toFun s)).trans (mem_orthogonal_iff.1 hv _ s.2).symm⟩

/-- Extending a form-preserving partial map by `v ↦ v'`, where `v'` has the pairings with the
image prescribed by `v`, again preserves the forms. -/
private lemma supSpanSingleton_isometry (hiso : ∀ x y : g.domain, ω₂ (g x) (g y) = ω₁ x y)
    {v : V} {v' : W} (hv : v ∉ g.domain) (hpair : ∀ s : g.domain, ω₂ (g s) v' = ω₁ s v)
    (x y : (g.supSpanSingleton v v' hv).domain) :
    ω₂ (g.supSpanSingleton v v' hv x) (g.supSpanSingleton v v' hv y) = ω₁ x y := by
  obtain ⟨s, c, hx, hgx⟩ := LinearPMap.exists_eq_add_smul_supSpanSingleton g v' hv x
  obtain ⟨t, d, hy, hgy⟩ := LinearPMap.exists_eq_add_smul_supSpanSingleton g v' hv y
  simp only [RingHom.id_apply] at hgx hgy
  rw [hgx, hgy, hx, hy]
  have h₁ := hpair s
  have h₂ : ω₂ v' (g t) = ω₁ v t := by rw [← ω₂.neg_eq, hpair t, ω₁.neg_eq]
  have h₃ := hiso s t
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    self_eq_zero] at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, h₃]

end PartialIsometry

/-- The induction behind Witt's theorem, on the codimension `n` of the domain of the partial
isometry. -/
private theorem exists_extend_aux [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (hdim : finrank ℝ V = finrank ℝ W) (n : ℕ) :
    ∀ g : V →ₗ.[ℝ] W, finrank ℝ V - finrank ℝ g.domain = n → Function.Injective g →
      (∀ x y : g.domain, ω₂ (g x) (g y) = ω₁ x y) →
      ∃ e : V ≃ₗ[ℝ] W, IsSymplectomorphism ω₁ ω₂ e ∧ ∀ x : g.domain, e x = g x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro g hn hinj hiso
  by_cases htop : g.domain = ⊤
  · -- A partial isometry defined everywhere is an injective linear map between spaces of the
    -- same dimension, hence a linear equivalence.
    have hG : Function.Injective (g.toFun ∘ₗ (LinearEquiv.ofTop g.domain htop).symm.toLinearMap) :=
      hinj.comp (LinearEquiv.injective _)
    have he : ∀ x : g.domain, LinearMap.linearEquivOfInjective _ hG hdim x = g x := fun x =>
      congr_arg g ((LinearEquiv.ofTop _ htop).symm_apply_apply x)
    have hmem : ∀ x : V, x ∈ g.domain := fun x => htop ▸ Submodule.mem_top
    refine ⟨_, isSymplectomorphism_iff.2 fun x y => ?_, he⟩
    rw [he ⟨x, hmem x⟩, he ⟨y, hmem y⟩, hiso]
  · obtain ⟨v, hv, v', hv', hpair⟩ := exists_extension_pair g hdim hinj hiso htop
    have hlt : g.domain < (g.supSpanSingleton v v' hv).domain :=
      lt_of_le_of_ne le_sup_left fun h =>
        hv (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self v))
    have hfin := Submodule.finrank_lt_finrank_of_lt hlt
    have hle := (g.supSpanSingleton v v' hv).domain.finrank_le
    obtain ⟨e, he, hext⟩ := ih _ (by omega) _ rfl
      (LinearPMap.supSpanSingleton_injective hinj hv hv')
      (supSpanSingleton_isometry g hiso hv hpair)
    exact ⟨e, he, fun x => (hext ⟨x, Submodule.mem_sup_left x.2⟩).trans
      (LinearPMap.supSpanSingleton_apply_mk_of_mem g v' hv x.2)⟩

/-- **Witt's extension theorem** for symplectic vector spaces. Between two finite-dimensional
symplectic vector spaces of the same dimension, an injective linear map from an arbitrary subspace
`S` preserving the restricted forms extends to a linear symplectomorphism. The subspace `S` need
not be symplectic: the restricted form may be degenerate of any rank. -/
theorem exists_isSymplectomorphism_extend [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (hdim : finrank ℝ V = finrank ℝ W)
    {S : Submodule ℝ V} (f : S →ₗ[ℝ] W) (hf : Function.Injective f)
    (hω : ∀ x y : S, ω₂ (f x) (f y) = ω₁ x y) :
    ∃ e : V ≃ₗ[ℝ] W, IsSymplectomorphism ω₁ ω₂ e ∧ ∀ x : S, e x = f x :=
  exists_extend_aux hdim _ ⟨S, f⟩ rfl hf hω

/-- **Witt's extension theorem**, for a linear isomorphism `f : S ≃ₗ[ℝ] T` between subspaces of two
symplectic vector spaces of the same finite dimension: if `f` preserves the restricted forms, it
is the restriction of a linear symplectomorphism. -/
theorem exists_isSymplectomorphism_extend_linearEquiv [FiniteDimensional ℝ V]
    [FiniteDimensional ℝ W] (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W)
    (hdim : finrank ℝ V = finrank ℝ W) {S : Submodule ℝ V} {T : Submodule ℝ W} (f : S ≃ₗ[ℝ] T)
    (hω : ∀ x y : S, ω₂ (f x) (f y) = ω₁ x y) :
    ∃ e : V ≃ₗ[ℝ] W, IsSymplectomorphism ω₁ ω₂ e ∧ ∀ x : S, e x = f x := by
  obtain ⟨e, he, hext⟩ := exists_isSymplectomorphism_extend ω₁ ω₂ hdim
    (T.subtype ∘ₗ f.toLinearMap) (T.injective_subtype.comp f.injective)
    fun x y => by simpa using hω x y
  exact ⟨e, he, fun x => by simpa using hext x⟩

/-- **Linear Darboux theorem.** Two symplectic vector spaces of the same finite dimension are
linearly symplectomorphic. -/
theorem exists_isSymplectomorphism [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (ω₁ : SymplecticForm V) (ω₂ : SymplecticForm W) (hdim : finrank ℝ V = finrank ℝ W) :
    ∃ e : V ≃ₗ[ℝ] W, IsSymplectomorphism ω₁ ω₂ e := by
  obtain ⟨e, he, -⟩ := exists_isSymplectomorphism_extend ω₁ ω₂ hdim
    (0 : (⊥ : Submodule ℝ V) →ₗ[ℝ] W) (Function.injective_of_subsingleton _) fun x y => by
      rw [Subsingleton.elim x 0]
      simp
  exact ⟨e, he⟩

end SymplecticForm

end TauCeti
