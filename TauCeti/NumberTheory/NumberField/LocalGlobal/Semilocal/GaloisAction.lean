/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# The Galois action on the semi-local algebra

Let `L/K` be an extension of number fields and `v` a finite place of `K`. An automorphism `σ` of
`L/K` acts on the semi-local algebra `K_v ⊗[K] L` through the second factor, by `id ⊗ σ`; this is
`semilocalGaloisHom`. Under the semi-local decomposition `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` it permutes
the factors: the component at `σ • w` of `(id ⊗ σ) z` is the component of `z` at `w`, transported
along the isomorphism of completions `L_w ≃ L_{σ • w}` induced by `σ`
(`semilocalEquiv_semilocalGaloisHom`). This is the action under which the adelic Galois action
of `L/K` restricts to the components above `v`
(`TauCeti.finiteAdeleSemilocalHom_finiteAdeleEquiv`).

When `L/K` is Galois, the Galois group permutes the places above `v` transitively, and the
stabilizer of one place `w` — its decomposition group — acts on `L_w`. The units of the
semi-local algebra are then **coinduced** from the decomposition group: as integral
representations of `Gal(L/K)`,

```text
(K_v ⊗[K] L)ˣ ≅ Coind_{D_w}^{Gal(L/K)} L_wˣ,
```

the map sending `y` to the function `g ↦ ((id ⊗ g) y)_w` (`semilocalUnitsCoindIso`). Shapiro's
lemma therefore computes the cohomology of the semi-local units from the local Galois
cohomology of `L_wˣ`.

## Main definitions

* `TauCeti.semilocalGaloisHom`: the action `σ ↦ id ⊗ σ` of `Aut(L/K)` on `K_v ⊗[K] L`.
* `TauCeti.semilocalUnitsRep`: the units of `K_v ⊗[K] L`, as an integral representation of
  `Aut(L/K)`.
* `TauCeti.decompositionUnitsRep`: the units of `L_w`, as an integral representation of the
  decomposition group of `w`.
* `TauCeti.semilocalUnitsToCoind`: the map `y ↦ (g ↦ ((id ⊗ g) y)_w)` into the coinduced
  representation.
* `TauCeti.semilocalUnitsCoindIso`: for `L/K` Galois, that map as an isomorphism of
  representations.

## Main results

* `TauCeti.semilocalEquiv_semilocalGaloisHom`: under the semi-local decomposition, `id ⊗ σ`
  carries the factor at `w` to the factor at `σ • w` by the isomorphism of completions.
* `TauCeti.semilocalUnitsCoindIso`: the semi-local units are coinduced from one completion.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §2 (the cohomology of `∏_{w ∣ v} L_wˣ`).
* J. Neukirch, *Algebraic Number Theory*, Chapter II, Proposition (8.3) and Chapter VI, §2.
-/

public section
noncomputable section

open IsDedekindDomain NumberField CategoryTheory
open scoped TensorProduct NumberField AdicCompletionExtension Pointwise

namespace TauCeti

open IsDedekindDomain.HeightOneSpectrum

local notation "𝒪" => _root_.NumberField.RingOfIntegers

section GaloisHom

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [Algebra K L]
  (v : HeightOneSpectrum (𝒪 K))

/-- The action of `Aut(L/K)` on the semi-local algebra `K_v ⊗[K] L` through the second factor:
`σ` acts by `id ⊗ σ`. -/
def semilocalGaloisHom :
    (L ≃ₐ[K] L) →*
      (v.adicCompletion K ⊗[K] L ≃ₐ[v.adicCompletion K] v.adicCompletion K ⊗[K] L) where
  toFun σ := Algebra.TensorProduct.congr AlgEquiv.refl σ
  map_one' := Algebra.TensorProduct.congr_refl
  map_mul' _ _ := AlgEquiv.coe_toAlgHom_injective (Algebra.TensorProduct.ext' fun _ _ ↦ rfl)

variable {L v}

/-- The Galois action on the semi-local algebra on a pure tensor. -/
@[simp]
theorem semilocalGaloisHom_tmul (σ : L ≃ₐ[K] L) (a : v.adicCompletion K) (x : L) :
    semilocalGaloisHom L v σ (a ⊗ₜ x) = a ⊗ₜ σ x :=
  (rfl)

variable [NumberField L]

/-- **The Galois action permutes the semi-local factors.** If `σ` carries the place `w` above `v`
to `w'`, then the component at `w'` of `(id ⊗ σ) z` is the component of `z` at `w`, transported
along the isomorphism of completions `L_w ≃ L_{w'}` induced by `σ`. -/
theorem semilocalEquiv_semilocalGaloisHom (σ : L ≃ₐ[K] L)
    {w w' : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}}
    (h : w'.1.asIdeal = σ • w.1.asIdeal) (z : v.adicCompletion K ⊗[K] L) :
    semilocalEquiv L v (semilocalGaloisHom L v σ z) w' =
      completionCongr v σ h (semilocalEquiv L v z w) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    rw [semilocalGaloisHom_tmul, semilocalEquiv_tmul, semilocalEquiv_tmul, map_mul,
      AlgEquiv.commutes, completionCongr_algebraMap]
  | add x y hx hy => simp [map_add, hx, hy]

end GaloisHom

section Coinduction

universe u

variable {K : Type u} [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
  [Algebra K L] (v : HeightOneSpectrum (𝒪 K))

/-- The units of the semi-local algebra `K_v ⊗[K] L`, as an integral representation of
`Aut(L/K)` acting through `semilocalGaloisHom`. -/
abbrev semilocalUnitsRep : Rep ℤ (L ≃ₐ[K] L) :=
  Rep.res (semilocalGaloisHom L v)
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (v.adicCompletion K ⊗[K] L))

variable {L} (w : HeightOneSpectrum (𝒪 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The units of the completion `L_w`, as an integral representation of the decomposition group
of `w` acting through `decompositionHom`. -/
abbrev decompositionUnitsRep : Rep ℤ (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal) :=
  Rep.res (decompositionHom v w)
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))

/-- The component at `w` of the semi-local units, an equivariant map for the decomposition
group of `w`. -/
private def semilocalUnitsComponent :
    Rep.res (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype (semilocalUnitsRep L v) ⟶
      decompositionUnitsRep v w :=
  Rep.ofHom ⟨(Units.map ((Pi.evalMonoidHom
      (fun w' : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal} ↦
        w'.1.adicCompletion L) ⟨w, ‹_›⟩).comp
      (semilocalEquiv L v : v.adicCompletion K ⊗[K] L →* _))).toAdditive.toIntLinearMap,
    fun d ↦ LinearMap.ext fun y : Additive (v.adicCompletion K ⊗[K] L)ˣ ↦
      Additive.toMul.injective <| Units.ext <|
        -- an element of the decomposition group fixes `w`, so it acts on the factor at `w`
        (semilocalEquiv_semilocalGaloisHom (w := ⟨w, ‹_›⟩) (w' := ⟨w, ‹_›⟩) (d : L ≃ₐ[K] L)
          (MulAction.mem_stabilizer_iff.mp d.2).symm _).trans
            (DFunLike.congr_fun (decompositionHom_apply d) _).symm⟩

/-- The map `y ↦ (g ↦ ((id ⊗ g) y)_w)` from the semi-local units to the representation
coinduced from the units of `L_w`. It is the morphism adjoint to the projection to the factor at
`w`, which is equivariant for the decomposition group of `w`. -/
def semilocalUnitsToCoind :
    semilocalUnitsRep L v ⟶
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype (decompositionUnitsRep v w) :=
  Rep.resCoindToHom _ _ _ (semilocalUnitsComponent v w)

/-- The value of `semilocalUnitsToCoind` at `g` is the component at `w` of `(id ⊗ g) y`. -/
theorem semilocalUnitsToCoind_apply (y : (v.adicCompletion K ⊗[K] L)ˣ) (g : L ≃ₐ[K] L) :
    ((Additive.toMul (α := (w.adicCompletion L)ˣ)
      (((semilocalUnitsToCoind v w).hom (Additive.ofMul y)).1 g) : (w.adicCompletion L)ˣ) :
        w.adicCompletion L) =
      semilocalEquiv L v (semilocalGaloisHom L v g y) ⟨w, ‹_›⟩ :=
  (rfl)

/-- For `L/K` Galois, every place above `v` is carried to `w` by some automorphism. -/
private theorem exists_asIdeal_eq_smul [IsGalois K L]
    (w' : {w' : HeightOneSpectrum (𝒪 L) // w'.asIdeal.LiesOver v.asIdeal}) :
    ∃ g : L ≃ₐ[K] L, w.asIdeal = g • w'.1.asIdeal := by
  have := w'.2
  obtain ⟨g, hg⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w'.1.asIdeal w.asIdeal (L ≃ₐ[K] L)
  exact ⟨g, hg.symm⟩

/-- Every automorphism carries some place above `v` to `w`, namely the translate of `w` by its
inverse. -/
private theorem exists_place_asIdeal_eq_smul (g : L ≃ₐ[K] L) :
    ∃ w' : {w' : HeightOneSpectrum (𝒪 L) // w'.asIdeal.LiesOver v.asIdeal},
      w.asIdeal = g • w'.1.asIdeal :=
  ⟨(liesOverEquivPrimesOver (𝒪 L) v).symm (g⁻¹ • liesOverEquivPrimesOver (𝒪 L) v ⟨w, ‹_›⟩), by
    rw [liesOverEquivPrimesOver_symm_apply, coe_smul_primesOver_ringOfIntegers,
      liesOverEquivPrimesOver_apply, smul_inv_smul]⟩

/-- For `L/K` Galois, a semi-local unit is determined by the components at `w` of its images
under all automorphisms of `L/K`. -/
private theorem semilocalUnitsToCoind_injective [IsGalois K L] :
    Function.Injective (semilocalUnitsToCoind v w).hom := by
  -- every place above `v` is carried to `w` by an automorphism, which transports the components
  intro y y' h
  obtain ⟨u, rfl⟩ : ∃ u : (v.adicCompletion K ⊗[K] L)ˣ, Additive.ofMul u = y := ⟨y.toMul, rfl⟩
  obtain ⟨u', rfl⟩ : ∃ u : (v.adicCompletion K ⊗[K] L)ˣ, Additive.ofMul u = y' := ⟨y'.toMul, rfl⟩
  refine congrArg Additive.ofMul (Units.ext ((semilocalEquiv L v).injective (funext fun w' ↦ ?_)))
  obtain ⟨g, hg⟩ := exists_asIdeal_eq_smul v w w'
  have := (semilocalUnitsToCoind_apply v w u g).symm.trans <|
    (congrArg (fun F ↦ ((Additive.toMul (α := (w.adicCompletion L)ˣ) (F.1 g) :
      (w.adicCompletion L)ˣ) : w.adicCompletion L)) h).trans (semilocalUnitsToCoind_apply v w u' g)
  rw [semilocalEquiv_semilocalGaloisHom g hg, semilocalEquiv_semilocalGaloisHom g hg] at this
  exact (completionCongr v g hg).injective this

/-- For `L/K` Galois, every function in the representation coinduced from the units of `L_w`
comes from a semi-local unit. -/
private theorem semilocalUnitsToCoind_surjective [IsGalois K L] :
    Function.Surjective (semilocalUnitsToCoind v w).hom := by
  intro F
  choose g hg using exists_asIdeal_eq_smul v w
  -- the component at `w'` is the value of `F` at an automorphism `g w'` carrying `w'` to `w`,
  -- transported back to `L_{w'}`; equivariance of `F` for the decomposition group makes the
  -- result independent of the choice of `g w'`
  let x : ∀ w' : {w' : HeightOneSpectrum (𝒪 L) // w'.asIdeal.LiesOver v.asIdeal},
      (w'.1.adicCompletion L)ˣ := fun w' ↦
    Units.map
      ((completionCongr v (g w') (hg w')).symm : w.adicCompletion L →* w'.1.adicCompletion L)
      (Additive.toMul (α := (w.adicCompletion L)ˣ) (F.1 (g w')))
  let y : (v.adicCompletion K ⊗[K] L)ˣ :=
    Units.map ((semilocalEquiv L v).symm : _ →* _) (MulEquiv.piUnits.symm x)
  refine ⟨Additive.ofMul y, Subtype.ext (funext fun σ ↦ ?_)⟩
  refine (Additive.toMul (α := (w.adicCompletion L)ˣ)).injective (Units.ext ?_)
  obtain ⟨w'', hw''⟩ := exists_place_asIdeal_eq_smul v w σ
  have hd : σ * (g w'')⁻¹ ∈ MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hg w'', inv_smul_smul, ← hw'']
    exact hg w''
  have hF := F.2 ⟨σ * (g w'')⁻¹, hd⟩ (g w'')
  rw [Subgroup.coe_subtype, inv_mul_cancel_right] at hF
  rw [semilocalUnitsToCoind_apply, semilocalEquiv_semilocalGaloisHom (w' := ⟨w, ‹_›⟩) σ hw'', hF]
  have hy : semilocalEquiv L v y w'' = x w'' := by
    simp [y]
  have hσ (a : w.adicCompletion L) :
      completionCongr v σ hw'' ((completionCongr v (g w'') (hg w'')).symm a) =
        decompositionHom v w ⟨σ * (g w'')⁻¹, hd⟩ a := by
    rw [← AlgEquiv.trans_apply, completionCongr_symm, completionCongr_trans,
      decompositionHom_apply]
  rw [hy]
  -- `x w''` and the action of `decompositionUnitsRep` on `F (g w'')` unfold to the two sides
  -- of `hσ`
  exact hσ _

/-- **The semi-local units are coinduced.** For `L/K` Galois and `w` a place above `v`, the units
of `K_v ⊗[K] L` are, as an integral representation of `Gal(L/K)`, coinduced from the units of
`L_w` as a representation of the decomposition group of `w`. -/
def semilocalUnitsCoindIso [IsGalois K L] :
    semilocalUnitsRep L v ≅
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype (decompositionUnitsRep v w) :=
  Rep.mkIso ((semilocalUnitsToCoind v w).hom.ofBijective
    ⟨semilocalUnitsToCoind_injective v w, semilocalUnitsToCoind_surjective v w⟩)

/-- The coinduction isomorphism is `semilocalUnitsToCoind`. -/
@[simp]
theorem semilocalUnitsCoindIso_hom [IsGalois K L] :
    (semilocalUnitsCoindIso v w).hom = semilocalUnitsToCoind v w :=
  (rfl)

end Coinduction

end TauCeti
