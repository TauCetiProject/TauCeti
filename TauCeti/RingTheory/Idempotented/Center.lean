/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.CentroidHom
public import Mathlib.CategoryTheory.Center.Preadditive
public import TauCeti.RingTheory.Idempotented.NondegMod

/-!
# Bimodule endomorphisms act on nondegenerate modules

Let `H` be an idempotented algebra over a commutative ring `A`. A bimodule endomorphism of `H`,
that is an additive map `φ : H → H` with `φ(xy) = x φ(y) = φ(x) y` (Mathlib's centroid
`CentroidHom H`), acts on every nondegenerate module `M` by `m ↦ φ(e) • m`, for any `e ∈ H` with
`e • m = m`. The value does not depend on `e`: for a local unit `f` of `e` and `e'`,
`φ(e) • m = (φ(f) e) • m = φ(f) • m`, and likewise for `e'`. These actions commute with module
homomorphisms, so they form an element of the centre of the category `NondegMod A H`.

This gives a ring homomorphism `CentroidHom H →+* CatCenter (NondegMod A H)`
(`TauCeti.NondegMod.centroidToCatCenter`), injective because on the nondegenerate part `H` of the
regular module of the unitization, `φ` acts by `x ↦ φ(x)`
(`TauCeti.NondegMod.centroidToCatCenter_injective`).

## Main definitions

* `CentroidHom.moduleEnd φ hM`: the action of `φ` on a nondegenerate module `M`.
* `TauCeti.NondegMod.centroidToCatCenter A H`: the ring homomorphism from the bimodule
  endomorphisms of `H` to the centre of `NondegMod A H`.

## Main results

* `CentroidHom.moduleEnd_apply_of_smul_eq`,
  `TauCeti.NondegMod.centroidToCatCenter_app_apply`: `φ` acts on `m` by `φ(e)` for every
  `e ∈ H` with `e • m = m`.
* `TauCeti.NondegMod.centroidToCatCenter_injective`: distinct bimodule endomorphisms act
  differently.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987
  manuscript, §1.1–1.2 and §1.8, pp. 3–4 and 8 (the centre of the category of nondegenerate
  modules and the bimodule endomorphisms of `H`).
-/

public section

universe v u₁ u₂

open CategoryTheory TauCeti

namespace CentroidHom

variable {A H : Type*} [CommSemiring A] [NonUnitalSemiring H] [Module A H]
  [IsScalarTower A H H] [SMulCommClass A H H] [IsIdempotented H]
  {M : Type*} [AddCommMonoid M] [Module (Unitization A H) M]

/-- A bimodule endomorphism `φ` of `H` gives the same action `φ(e) • m = φ(e') • m` through any
two elements `e, e'` of `H` fixing `m`: both equal `φ(f) • m` for a local unit `f` of `e` and
`e'`. -/
theorem inr_apply_smul_eq_of_smul_eq (φ : CentroidHom H) {m : M} {e e' : H}
    (he : (e : Unitization A H) • m = m) (he' : (e' : Unitization A H) • m = m) :
    (φ e : Unitization A H) • m = (φ e' : Unitization A H) • m := by
  classical
  obtain ⟨f, -, hf⟩ := IsIdempotented.exists_isIdempotentElem {e, e'}
  have key {e : H} (hfe : f * e = e) (he : (e : Unitization A H) • m = m) :
      (φ e : Unitization A H) • m = (φ f : Unitization A H) • m := by
    rw [← hfe, map_mul_right, Unitization.inr_mul, mul_smul, he]
  rw [key (hf e (by simp)).1 he, key (hf e' (by simp)).1 he']

/-- The action `m ↦ φ(e) • m` of a bimodule endomorphism `φ` of `H` on a nondegenerate module
`M`, where `e ∈ H` is any element with `e • m = m` (`CentroidHom.moduleEnd_apply_of_smul_eq`). -/
noncomputable def moduleEnd (φ : CentroidHom H) (hM : IsNondegenerate A H M) :
    M →ₗ[Unitization A H] M := by
  classical
  let act : M →+ M :=
    { toFun m := (φ (isNondegenerate_iff.1 hM m).choose : Unitization A H) • m
      map_zero' := by rw [smul_zero]
      map_add' m m' := by
        obtain ⟨f, -, hf⟩ := hM.exists_isIdempotentElem_forall_smul_eq {m, m'}
        have h (x : M) (hx : (f : Unitization A H) • x = x) :
            (φ (isNondegenerate_iff.1 hM x).choose : Unitization A H) • x =
              (φ f : Unitization A H) • x :=
          φ.inr_apply_smul_eq_of_smul_eq (isNondegenerate_iff.1 hM x).choose_spec.2 hx
        rw [h _ (by rw [smul_add, hf m (by simp), hf m' (by simp)]), h m (hf m (by simp)),
          h m' (hf m' (by simp)), smul_add] }
  refine
    { toFun := act
      map_add' := act.map_add
      map_smul' := hM.map_smul_of_map_inr_smul act fun h m ↦ ?_ }
  -- Take a two-sided local unit `f` of `h` and of a local unit `e` of `m`; then `f` fixes `m` and
  -- `h • m`, and both sides are `φ(h) • m`.
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  obtain ⟨f, -, hf⟩ := IsIdempotented.exists_isIdempotentElem {h, e}
  have hfm : (f : Unitization A H) • m = m := inr_smul_eq_of_mul_eq he (hf e (by simp)).1
  have hfhm : (f : Unitization A H) • (h : Unitization A H) • m = (h : Unitization A H) • m := by
    rw [smul_smul, ← Unitization.inr_mul, (hf h (by simp)).1]
  have hact (x : M) (hx : (f : Unitization A H) • x = x) :
      act x = (φ f : Unitization A H) • x :=
    φ.inr_apply_smul_eq_of_smul_eq (isNondegenerate_iff.1 hM x).choose_spec.2 hx
  rw [hact _ hfhm, hact m hfm, smul_smul, smul_smul, ← Unitization.inr_mul,
    ← Unitization.inr_mul, ← map_mul_right, ← map_mul_left,
    (hf h (by simp)).1, (hf h (by simp)).2]

/-- A bimodule endomorphism `φ` acts on `m` by `φ(e)`, for any `e ∈ H` with `e • m = m`. -/
theorem moduleEnd_apply_of_smul_eq (φ : CentroidHom H) (hM : IsNondegenerate A H M) {m : M}
    {e : H} (he : (e : Unitization A H) • m = m) :
    φ.moduleEnd hM m = (φ e : Unitization A H) • m :=
  φ.inr_apply_smul_eq_of_smul_eq (isNondegenerate_iff.1 hM m).choose_spec.2 he

/-- A bimodule endomorphism commutes with homomorphisms of nondegenerate modules. -/
theorem moduleEnd_comp {N : Type*} [AddCommMonoid N] [Module (Unitization A H) N]
    (φ : CentroidHom H) (hM : IsNondegenerate A H M) (hN : IsNondegenerate A H N)
    (g : M →ₗ[Unitization A H] N) :
    φ.moduleEnd hN ∘ₗ g = g ∘ₗ φ.moduleEnd hM := by
  ext m
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  have hge : (e : Unitization A H) • g m = g m := by rw [← map_smul, he]
  simp only [LinearMap.comp_apply]
  rw [φ.moduleEnd_apply_of_smul_eq hN hge, φ.moduleEnd_apply_of_smul_eq hM he, map_smul]

end CentroidHom

namespace TauCeti.NondegMod

variable {A : Type u₁} {H : Type u₂} [CommRing A] [NonUnitalRing H] [Module A H]
  [IsScalarTower A H H] [SMulCommClass A H H] [IsIdempotented H]

variable (A H)

/-- The element of the centre of `NondegMod A H` given by a bimodule endomorphism `φ` of `H`,
acting on each nondegenerate module `M` by `m ↦ φ(e) • m` for a local unit `e` of `m`. -/
private noncomputable def centroidToCatCenterAux (φ : CentroidHom H) :
    CatCenter (NondegMod.{v} A H) :=
  .of
    { app M := ObjectProperty.homMk
        (ModuleCat.ofHom (φ.moduleEnd M.isNondegenerate))
      naturality M N g := by
        ext m
        have := LinearMap.congr_fun
          (φ.moduleEnd_comp M.isNondegenerate N.isNondegenerate g.hom.hom) m
        simp only [LinearMap.comp_apply] at this
        simpa using this }

variable {A H} in
private theorem centroidToCatCenterAux_app_apply (φ : CentroidHom H) (M : NondegMod.{v} A H)
    {m : M.obj} {e : H} (he : (e : Unitization A H) • m = m) :
    ((centroidToCatCenterAux.{v} A H φ).app M).hom.hom m = (φ e : Unitization A H) • m :=
  φ.moduleEnd_apply_of_smul_eq M.isNondegenerate he

/-- **Bimodule endomorphisms of `H` give central endomorphisms of nondegenerate modules.** The
ring homomorphism from the centroid of `H` to the centre of `NondegMod A H`, sending `φ` to the
natural transformation `m ↦ φ(e) • m` (`e` a local unit of `m`). -/
noncomputable def centroidToCatCenter : CentroidHom H →+* CatCenter (NondegMod.{v} A H) where
  toFun := centroidToCatCenterAux.{v} A H
  map_one' := by
    ext M m
    obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 M.isNondegenerate m
    rw [centroidToCatCenterAux_app_apply _ M he, CentroidHom.one_apply, he]
    rw [CatCenter.app_one, ObjectProperty.FullSubcategory.id_hom, ModuleCat.hom_id,
      LinearMap.id_apply]
  map_mul' φ ψ := by
    ext M m
    obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 M.isNondegenerate m
    -- A local unit `f` of `ψ(e)` fixes `ψ(e) • m`, and `φ(f) ψ(e) = φ(f ψ(e)) = φ(ψ(e))`.
    obtain ⟨f, -, hf⟩ := IsIdempotented.exists_isIdempotentElem {ψ e}
    have hfψ : f * ψ e = ψ e := (hf (ψ e) (by simp)).1
    have hfm :
        (f : Unitization A H) • (ψ e : Unitization A H) • m = (ψ e : Unitization A H) • m := by
      rw [smul_smul, ← Unitization.inr_mul, hfψ]
    rw [CatCenter.mul_app', ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp,
      LinearMap.comp_apply, centroidToCatCenterAux_app_apply ψ M he,
      centroidToCatCenterAux_app_apply φ M hfm, centroidToCatCenterAux_app_apply (φ * ψ) M he,
      smul_smul, ← Unitization.inr_mul, ← map_mul_right, hfψ, CentroidHom.mul_apply]
  map_zero' := by
    ext M m
    obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 M.isNondegenerate m
    rw [centroidToCatCenterAux_app_apply _ M he, CentroidHom.zero_apply, Unitization.inr_zero,
      zero_smul]
    rw [CatCenter.app_zero, ObjectProperty.zero_hom, ModuleCat.hom_zero, LinearMap.zero_apply]
  map_add' φ ψ := by
    ext M m
    obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 M.isNondegenerate m
    rw [CatCenter.app_add, ← ObjectProperty.ι_map (f := _ + _), Functor.map_add, ModuleCat.hom_add,
      LinearMap.add_apply, ObjectProperty.ι_map, ObjectProperty.ι_map]
    rw [centroidToCatCenterAux_app_apply _ M he, centroidToCatCenterAux_app_apply _ M he,
      centroidToCatCenterAux_app_apply _ M he, CentroidHom.add_apply, Unitization.inr_add,
      add_smul]

variable {A H}

/-- A bimodule endomorphism `φ` acts on an element `m` of a nondegenerate module by `φ(e)`, for any
`e ∈ H` with `e • m = m`. -/
theorem centroidToCatCenter_app_apply (φ : CentroidHom H) (M : NondegMod.{v} A H) {m : M.obj}
    {e : H} (he : (e : Unitization A H) • m = m) :
    ((centroidToCatCenter.{v} A H φ).app M).hom.hom m = (φ e : Unitization A H) • m :=
  centroidToCatCenterAux_app_apply φ M he

/-- **Distinct bimodule endomorphisms act differently** on nondegenerate modules: on the
nondegenerate part `H` of the regular module of the unitization, `φ` acts by `x ↦ φ(x)`. -/
theorem centroidToCatCenter_injective :
    Function.Injective (centroidToCatCenter.{max u₁ u₂} A H) := by
  classical
  intro φ ψ h
  ext x
  obtain ⟨e, -, he⟩ := IsIdempotented.exists_isIdempotentElem {x}
  have hex : e * x = x := (he x (by simp)).1
  let X : NondegMod.{max u₁ u₂} A H :=
    ⟨ModuleCat.of _ (nondegeneratePart A H (Unitization A H)),
      (nondegenerateModuleProperty_iff _).2 isNondegenerate_nondegeneratePart⟩
  have hx : (x : Unitization A H) ∈ nondegeneratePart A H (Unitization A H) := by
    simpa [← Unitization.inr_mul, hex] using
      inr_smul_mem_nondegeneratePart (A := A) e (x : Unitization A H)
  let m : nondegeneratePart A H (Unitization A H) := ⟨x, hx⟩
  have hm : (e : Unitization A H) • (m : X.obj) = m := by
    refine Subtype.ext ?_
    rw [Submodule.coe_smul, smul_eq_mul, ← Unitization.inr_mul, hex]
  have := congrArg (fun z : CatCenter (NondegMod.{max u₁ u₂} A H) ↦
    ((z.app X).hom.hom m).val) h
  simp only [centroidToCatCenter_app_apply _ X hm] at this
  rw [Submodule.coe_smul, Submodule.coe_smul, smul_eq_mul, smul_eq_mul] at this
  rwa [← Unitization.inr_mul, ← Unitization.inr_mul, ← map_mul_right, ← map_mul_right, hex,
    Unitization.inr_injective.eq_iff] at this

end TauCeti.NondegMod
