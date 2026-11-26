/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RingTheory.OrzechProperty
public import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Weak semisimplicity at the eigenvalue one

For an endomorphism `f` of a module `M`, the *invariants* of `f` are its fixed submodule
`f.fixedSubmodule = ker (f - 1)` and its *coinvariants* are the quotient `M ⧸ range (f - 1)`.
Including invariants into `M` and projecting to coinvariants gives the canonical map
`Module.End.invariantCoinvariantMap f`, and `f` is *weakly semisimple* when this map is
bijective. Equivalently `M` is the internal direct sum of `ker (f - 1)` and `range (f - 1)`.

This is the setting of Liu–Tian–Xiao–Zhang–Zhu, where `f` is the action of a topological
generator of a procyclic group on a finite-type `ℤ_p`-module or a finite-dimensional
`ℚ_p`-vector space, and weak semisimplicity makes the invariants of the group map isomorphically
onto its coinvariants. The condition only concerns the eigenvalue one: it is implied by
semisimplicity, but a nonsemisimple endomorphism `f` for which `f - 1` is invertible is weakly
semisimple.

## Main definitions

* `Module.End.invariantCoinvariantMap`: the map from invariants to coinvariants.
* `Module.End.IsWeaklySemisimple`: the invariants-to-coinvariants map is bijective.
* `Module.End.IsWeaklySemisimple.invariantCoinvariantEquiv`: the resulting linear equivalence.

## Main results

* `Module.End.isWeaklySemisimple_iff_isCompl`: weak semisimplicity is the decomposition
  `M = ker (f - 1) ⊕ range (f - 1)`.
* `LinearEquiv.isWeaklySemisimple_iff`: an intertwining linear equivalence preserves it.
* `Module.End.isWeaklySemisimple_prodMap_iff`, `Module.End.isWeaklySemisimple_piMap_iff`: a
  product of endomorphisms is weakly semisimple exactly when every factor is.
* `Module.End.IsSemisimple.isWeaklySemisimple`: semisimple endomorphisms are weakly semisimple.
* `Module.End.isWeaklySemisimple_iff_surjective`: on a finite module over a ring with the Orzech
  property (for instance any commutative ring), surjectivity of the invariants-to-coinvariants
  map already implies bijectivity; in particular vanishing coinvariants force vanishing
  invariants (`Module.End.fixedSubmodule_eq_bot_of_range_sub_one_eq_top`).
* `TauCeti.not_isWeaklySemisimple_toLin'_unipotent`,
  `TauCeti.isWeaklySemisimple_toLin'_jordanBlock_two` and
  `TauCeti.not_isSemisimple_toLin'_jordanBlock_two`: the two-dimensional unipotent Jordan block
  is not weakly semisimple, while the Jordan block with eigenvalue `2` is weakly semisimple
  without being semisimple.

## References

* Y. Liu, Y. Tian, L. Xiao, W. Zhang, X. Zhu, *On the Beilinson–Bloch–Kato conjecture for
  Rankin–Selberg motives*, Invent. Math. 228 (2022), §2.1 (Definition 2.1.2 and the lemmas
  following it).
-/

public section

open LinearMap Submodule

namespace Module.End

section Ring

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The canonical map from the invariants `ker (f - 1)` of an endomorphism `f` to its
coinvariants `M ⧸ range (f - 1)`: inclusion followed by the quotient map. -/
def invariantCoinvariantMap (f : End R M) : f.fixedSubmodule →ₗ[R] M ⧸ range (f - 1) :=
  (range (f - 1)).mkQ ∘ₗ f.fixedSubmodule.subtype

theorem invariantCoinvariantMap_def (f : End R M) :
    f.invariantCoinvariantMap = (range (f - 1)).mkQ ∘ₗ f.fixedSubmodule.subtype :=
  (rfl)

@[simp]
theorem invariantCoinvariantMap_apply (f : End R M) (x : f.fixedSubmodule) :
    f.invariantCoinvariantMap x = Submodule.Quotient.mk (x : M) :=
  (rfl)

/-- The invariants-to-coinvariants map is injective exactly when no nonzero fixed vector lies in
the range of `f - 1`. -/
theorem injective_invariantCoinvariantMap_iff (f : End R M) :
    Function.Injective f.invariantCoinvariantMap ↔
      Disjoint f.fixedSubmodule (range (f - 1)) := by
  rw [← LinearMap.ker_eq_bot, invariantCoinvariantMap_def, LinearMap.ker_comp, ker_mkQ,
    disjoint_iff_comap_eq_bot]

/-- The invariants-to-coinvariants map is surjective exactly when fixed vectors and the range
of `f - 1` together span the module. -/
theorem surjective_invariantCoinvariantMap_iff (f : End R M) :
    Function.Surjective f.invariantCoinvariantMap ↔
      Codisjoint f.fixedSubmodule (range (f - 1)) := by
  rw [← LinearMap.range_eq_top, invariantCoinvariantMap_def, LinearMap.range_comp, range_subtype,
    map_mkQ_eq_top, codisjoint_iff, sup_comm]

/-- An endomorphism is *weakly semisimple* (at the eigenvalue one) when the canonical map from
its invariants `ker (f - 1)` to its coinvariants `M ⧸ range (f - 1)` is bijective. -/
def IsWeaklySemisimple (f : End R M) : Prop :=
  Function.Bijective f.invariantCoinvariantMap

/-- Weak semisimplicity is the decomposition `M = ker (f - 1) ⊕ range (f - 1)`. -/
theorem isWeaklySemisimple_iff_isCompl (f : End R M) :
    f.IsWeaklySemisimple ↔ IsCompl f.fixedSubmodule (range (f - 1)) := by
  rw [IsWeaklySemisimple, Function.Bijective, injective_invariantCoinvariantMap_iff,
    surjective_invariantCoinvariantMap_iff, isCompl_iff]

/-- The linear equivalence between the invariants and the coinvariants of a weakly semisimple
endomorphism. -/
noncomputable def IsWeaklySemisimple.invariantCoinvariantEquiv {f : End R M}
    (hf : f.IsWeaklySemisimple) : f.fixedSubmodule ≃ₗ[R] M ⧸ range (f - 1) :=
  (quotientEquivOfIsCompl _ _ ((isWeaklySemisimple_iff_isCompl f).mp hf).symm).symm

@[simp]
theorem IsWeaklySemisimple.invariantCoinvariantEquiv_apply {f : End R M}
    (hf : f.IsWeaklySemisimple) (x : f.fixedSubmodule) :
    hf.invariantCoinvariantEquiv x = Submodule.Quotient.mk (x : M) :=
  (rfl)

@[simp]
theorem IsWeaklySemisimple.toLinearMap_invariantCoinvariantEquiv {f : End R M}
    (hf : f.IsWeaklySemisimple) :
    (hf.invariantCoinvariantEquiv : f.fixedSubmodule →ₗ[R] M ⧸ range (f - 1)) =
      f.invariantCoinvariantMap :=
  (rfl)

/-- The inverse of the invariants-to-coinvariants equivalence sends the class of `x` to the
invariant component of `x` in the decomposition `M = ker (f - 1) ⊕ range (f - 1)`. -/
@[simp]
theorem IsWeaklySemisimple.invariantCoinvariantEquiv_symm_mk {f : End R M}
    (hf : f.IsWeaklySemisimple) (x : M) :
    hf.invariantCoinvariantEquiv.symm (Submodule.Quotient.mk x) =
      f.fixedSubmodule.projectionOnto (range (f - 1))
        ((isWeaklySemisimple_iff_isCompl f).mp hf) x :=
  (rfl)

/-- The identity is weakly semisimple: everything is invariant and the coinvariants are the
whole module. -/
theorem isWeaklySemisimple_one : (1 : End R M).IsWeaklySemisimple := by
  rw [isWeaklySemisimple_iff_isCompl, sub_self, LinearMap.range_zero,
    fixedSubmodule_eq_top_iff.mpr one_eq_id]
  exact isCompl_top_bot

/-- If `f - 1` is invertible, then the invariants and coinvariants of `f` both vanish, so `f` is
weakly semisimple. -/
theorem isWeaklySemisimple_of_isUnit_sub_one {f : End R M} (hf : IsUnit (f - 1)) :
    f.IsWeaklySemisimple := by
  rw [isUnit_iff] at hf
  rw [isWeaklySemisimple_iff_isCompl, fixedSubmodule_eq_ker, ← one_eq_id,
    LinearMap.ker_eq_bot.mpr hf.injective, LinearMap.range_eq_top.mpr hf.surjective]
  exact isCompl_bot_top

/-- An intertwining linear equivalence preserves weak semisimplicity. -/
protected theorem _root_.LinearEquiv.isWeaklySemisimple_iff (f : End R M) (g : End R N)
    (e : M ≃ₗ[R] N) (he : e ∘ₗ f = g ∘ₗ e) :
    f.IsWeaklySemisimple ↔ g.IsWeaklySemisimple := by
  have hrange : (range (f - 1)).map (e : M →ₗ[R] N) = range (g - 1) := by
    have hcomp : (e : M →ₗ[R] N) ∘ₗ (f - 1) = (g - 1) ∘ₗ e := by
      ext x
      simpa using LinearMap.congr_fun he x
    rw [← LinearMap.range_comp, hcomp, LinearMap.range_comp_of_range_eq_top _ e.range]
  rw [isWeaklySemisimple_iff_isCompl, isWeaklySemisimple_iff_isCompl,
    (orderIsoMapComap e).isCompl_iff, orderIsoMapComap_apply, orderIsoMapComap_apply,
    e.map_fixedSubmodule he, hrange]

/-- A product of two endomorphisms is weakly semisimple exactly when both factors are. -/
theorem isWeaklySemisimple_prodMap_iff (f : End R M) (g : End R N) :
    IsWeaklySemisimple (f.prodMap g) ↔ f.IsWeaklySemisimple ∧ g.IsWeaklySemisimple := by
  have hsub : f.prodMap g - 1 = (f - 1).prodMap (g - 1) := by
    ext <;> simp
  simp only [isWeaklySemisimple_iff_isCompl, fixedSubmodule_prodMap, hsub, range_prodMap,
    isCompl_iff, disjoint_iff, codisjoint_iff, prod_inf_prod, prod_sup_prod, prod_eq_bot_iff,
    prod_eq_top_iff]
  tauto

/-- A componentwise endomorphism of a product is weakly semisimple exactly when every component
is. The index type need not be finite. -/
theorem isWeaklySemisimple_piMap_iff {ι : Type*} {W : ι → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module R (W i)] (g : ∀ i, End R (W i)) :
    IsWeaklySemisimple (LinearMap.piMap g) ↔ ∀ i, (g i).IsWeaklySemisimple := by
  classical
  have hsub (w : ∀ i, W i) (i : ι) : (LinearMap.piMap g - 1) w i = (g i - 1) (w i) := by
    simp
  simp only [isWeaklySemisimple_iff_isCompl, isCompl_iff, Submodule.disjoint_def,
    codisjoint_iff_exists_add_eq, mem_fixedSubmodule_iff, LinearMap.mem_range, forall_and]
  refine and_congr ⟨fun h i x hx ⟨y, hy⟩ ↦ ?_, fun h w hw ⟨y, hy⟩ ↦ ?_⟩
    ⟨fun h i x ↦ ?_, fun h w ↦ ?_⟩
  · -- A fixed vector in the range of `g i - 1` gives one for the product, supported at `i`.
    have hfix : LinearMap.piMap g (Pi.single i x) = Pi.single i x := funext fun j ↦ by
      rcases eq_or_ne j i with rfl | hj
      · simpa using hx
      · simp [hj]
    have := h (Pi.single i x) hfix ⟨Pi.single i y, funext fun j ↦ ?_⟩
    · simpa using congrFun this i
    · rcases eq_or_ne j i with rfl | hj
      · simpa [hsub] using hy
      · simp [hsub, hj]
  · exact funext fun i ↦ h i (w i) (congrFun hw i) ⟨y i, by rw [← hsub, hy]⟩
  · obtain ⟨u, v, hu, ⟨y, rfl⟩, huv⟩ := h (Pi.single i x)
    exact ⟨u i, (g i - 1) (y i), congrFun hu i, ⟨y i, rfl⟩, by
      simpa [hsub] using congrFun huv i⟩
  · choose u v hu hv huv using fun i ↦ h i (w i)
    choose y hy using hv
    exact ⟨u, LinearMap.piMap g y - y, funext hu, ⟨y, rfl⟩, funext fun i ↦ by
      simpa [← hy] using huv i⟩

end Ring

section Finite

variable {R M : Type*} [Ring R] [OrzechProperty R] [AddCommGroup M] [Module R M]
  [Module.Finite R M]

/-- On a finite module over a ring with the Orzech property, such as any commutative ring, an
endomorphism is weakly semisimple as soon as its invariants-to-coinvariants map is surjective. -/
theorem isWeaklySemisimple_iff_surjective (f : End R M) :
    f.IsWeaklySemisimple ↔ Function.Surjective f.invariantCoinvariantMap := by
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
  -- `f - 1` maps its range `I` onto itself, since `M = ker (f - 1) + I`. The range is a
  -- finite module, so this surjective endomorphism `ψ` of `I` is injective, and
  -- `ker ψ = ker (f - 1) ⊓ I`.
  rw [surjective_invariantCoinvariantMap_iff, codisjoint_iff_exists_add_eq] at h
  rw [injective_invariantCoinvariantMap_iff, Submodule.disjoint_def]
  let ψ : range (f - 1) →ₗ[R] range (f - 1) :=
    (f - 1).restrict fun x _ ↦ mem_range_self (f - 1) x
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, x, rfl⟩
    obtain ⟨k, i, hk, hi, rfl⟩ := h x
    refine ⟨⟨i, hi⟩, Subtype.ext ?_⟩
    rw [mem_fixedSubmodule_iff] at hk
    simp [ψ, hk]
  intro x hx hxr
  rw [mem_fixedSubmodule_iff] at hx
  have hψx : ψ ⟨x, hxr⟩ = ψ 0 := Subtype.ext (by simp [ψ, hx])
  simpa using congrArg Subtype.val (OrzechProperty.injective_of_surjective_endomorphism ψ hψ hψx)

/-- On a finite module over a ring with the Orzech property, such as any commutative ring,
vanishing coinvariants force vanishing invariants. -/
theorem fixedSubmodule_eq_bot_of_range_sub_one_eq_top {f : End R M}
    (hf : range (f - 1) = ⊤) : f.fixedSubmodule = ⊥ := by
  have hws : f.IsWeaklySemisimple := by
    rw [isWeaklySemisimple_iff_surjective, surjective_invariantCoinvariantMap_iff, hf]
    exact codisjoint_top_right
  rw [isWeaklySemisimple_iff_isCompl, hf] at hws
  exact disjoint_top.mp hws.disjoint

end Finite

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A semisimple endomorphism is weakly semisimple. No finiteness assumption is needed. -/
theorem IsSemisimple.isWeaklySemisimple {f : End R M} (hf : f.IsSemisimple) :
    f.IsWeaklySemisimple := by
  -- Work with `g = f - 1`, which is semisimple too, and use `g`-invariant complements.
  have hg : (f - 1).IsSemisimple := by
    have := (isSemisimple_sub_algebraMap_iff (f := f) (μ := (1 : R))).mpr hf
    rwa [map_one] at this
  set g := f - 1
  have hker : LinearMap.ker g ∈ g.invtSubmodule := by
    rw [mem_invtSubmodule]
    intro x hx
    rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker.mp hx, map_zero]
  have hrange (p : Submodule R M) : LinearMap.range g ≤ p → p ∈ g.invtSubmodule := by
    intro hp
    rw [mem_invtSubmodule]
    exact fun x _ ↦ hp (mem_range_self g x)
  rw [isWeaklySemisimple_iff_isCompl, fixedSubmodule_eq_ker, ← one_eq_id, isCompl_iff]
  refine ⟨?_, ?_⟩
  · -- `x = g y` with `g x = 0`; decompose `y` along an invariant complement `q` of `ker g`.
    obtain ⟨q, hq, hkq⟩ := isSemisimple_iff.mp hg _ hker
    rw [Submodule.disjoint_def]
    rintro _ hx ⟨y, rfl⟩
    obtain ⟨k, z, hk, hz, rfl⟩ := codisjoint_iff_exists_add_eq.mp hkq.codisjoint y
    have hgz : g (k + z) = g z := by simp [LinearMap.mem_ker.mp hk]
    rw [hgz] at hx ⊢
    exact Submodule.disjoint_def.mp hkq.disjoint _ hx ((mem_invtSubmodule g).mp hq hz)
  · -- An invariant complement `q` of `ker g ⊔ range g` satisfies `g q = 0`, so `q = 0`.
    obtain ⟨q, hq, hpq⟩ :=
      isSemisimple_iff.mp hg _ (hrange (LinearMap.ker g ⊔ LinearMap.range g) le_sup_right)
    have hq_bot : q = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hgz : g z = 0 := Submodule.disjoint_def.mp hpq.disjoint _
        (mem_sup_right (mem_range_self g z)) ((mem_invtSubmodule g).mp hq hz)
      exact Submodule.disjoint_def.mp hpq.disjoint _ (mem_sup_left hgz) hz
    rw [codisjoint_iff, ← hpq.sup_eq_top, hq_bot, sup_bot_eq]

end CommRing

end Module.End

namespace TauCeti

open Matrix Module.End

variable {R : Type*} [CommRing R]

/-- The two-dimensional unipotent Jordan block `!![1, 1; 0, 1]` is not weakly semisimple: its
nonzero fixed vector `![1, 0]` maps to zero in the coinvariants. -/
theorem not_isWeaklySemisimple_toLin'_unipotent [Nontrivial R] :
    ¬ IsWeaklySemisimple (toLin' !![(1 : R), 1; 0, 1]) := by
  -- `![1, 0]` is fixed and is the image of `![0, 1]` under `σ - 1`.
  rw [isWeaklySemisimple_iff_isCompl]
  intro h
  have hfix : ![(1 : R), 0] ∈ (toLin' !![(1 : R), 1; 0, 1]).fixedSubmodule := by
    rw [LinearMap.mem_fixedSubmodule_iff]
    ext i
    fin_cases i <;> simp
  have hrange : ![(1 : R), 0] ∈ LinearMap.range (toLin' !![(1 : R), 1; 0, 1] - 1) :=
    ⟨![0, 1], by ext i; fin_cases i <;> simp⟩
  simpa using congrFun (Submodule.disjoint_def.mp h.disjoint _ hfix hrange) 0

/-- The Jordan block `!![2, 1; 0, 2]` is weakly semisimple: `σ - 1` is invertible, so its
invariants and coinvariants both vanish. -/
theorem isWeaklySemisimple_toLin'_jordanBlock_two :
    IsWeaklySemisimple (toLin' !![(2 : R), 1; 0, 2]) := by
  apply isWeaklySemisimple_of_isUnit_sub_one
  have hsub : toLin' !![(2 : R), 1; 0, 2] - 1 = toLinAlgEquiv' !![(1 : R), 1; 0, 1] := by
    ext v i
    fin_cases v <;> fin_cases i <;> simp [toLinAlgEquiv'_apply] <;> norm_num
  rw [hsub]
  refine IsUnit.map _ ?_
  rw [Matrix.isUnit_iff_isUnit_det, det_fin_two_of]
  simp

/-- The Jordan block `!![2, 1; 0, 2]` is not semisimple. Together with
`isWeaklySemisimple_toLin'_jordanBlock_two`, this shows that weak semisimplicity is strictly
weaker than semisimplicity. -/
theorem not_isSemisimple_toLin'_jordanBlock_two [Nontrivial R] :
    ¬ Module.End.IsSemisimple (toLin' !![(2 : R), 1; 0, 2]) := by
  -- Subtracting `2` would leave a semisimple, nonzero nilpotent endomorphism.
  intro h
  have hsub : toLin' !![(2 : R), 1; 0, 2] - algebraMap R (Module.End R (Fin 2 → R)) 2 =
      toLinAlgEquiv' !![(0 : R), 1; 0, 0] := by
    ext v i
    fin_cases v <;> fin_cases i <;> simp [toLinAlgEquiv'_apply]
  have hnil : IsNilpotent (toLinAlgEquiv' !![(0 : R), 1; 0, 0]) := by
    refine IsNilpotent.map ⟨2, ?_⟩ _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq]
  have h0 := eq_zero_of_isNilpotent_isSemisimple hnil
    (hsub ▸ isSemisimple_sub_algebraMap_iff.mpr h)
  rw [map_eq_zero_iff _ toLinAlgEquiv'.injective] at h0
  simpa using congrFun (congrFun h0 0) 1

end TauCeti
