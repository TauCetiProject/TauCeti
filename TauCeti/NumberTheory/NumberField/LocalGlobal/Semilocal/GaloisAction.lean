/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import TauCeti.NumberTheory.NumberField.LocalGlobal.DecompositionGroup
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Basic
public import TauCeti.NumberTheory.NumberField.LocalGlobal.Semilocal.Galois
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# The Galois action on the semi-local algebra

Let `L/K` be an extension of number fields and `v` a finite place of `K`. An automorphism `σ` of
`L/K` acts on the semi-local algebra `K_v ⊗[K] L` through the second factor, by `id ⊗ σ`; this is
`TauCeti.semilocalGaloisHom`, defined for an arbitrary base algebra. Under the semi-local
decomposition `K_v ⊗[K] L ≃ ∏_{w ∣ v} L_w` it permutes the factors: the component at `σ • w` of
`(id ⊗ σ) z` is the component of `z` at `w`, transported along the isomorphism of completions
`L_w ≃ L_{σ • w}` induced by `σ` (`semilocalEquiv_semilocalGaloisHom`). This is the action under
which the adelic Galois action of `L/K` restricts to the components above `v`
(`TauCeti.finiteAdeleSemilocalHom_finiteAdeleEquiv`).

When `L/K` is Galois, the Galois group permutes the places above `v` transitively, and the
stabilizer of one place `w` — its decomposition group — acts on `L_w`. The units of the
semi-local algebra are then **coinduced** from the decomposition group: as integral
representations of `Gal(L/K)`,

```text
(K_v ⊗[K] L)ˣ ≅ Coind_{D_w}^{Gal(L/K)} L_wˣ,
```

the map sending `y` to the function `g ↦ ((id ⊗ g) y)_w` (`semilocalUnitsCoindIso`); its
bijectivity is an instance of `TauCeti.semilocal_eq_of_forall_component_eq` and
`TauCeti.semilocal_exists_forall_component_eq`. Shapiro's
lemma therefore computes the cohomology of the semi-local units from the local Galois
cohomology of `L_wˣ`.

## Main definitions

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

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝒪 K)}

/-- **The Galois action permutes the semi-local factors.** If `σ` carries the place `w` above `v`
to `w'`, then the component at `w'` of `(id ⊗ σ) z` is the component of `z` at `w`, transported
along the isomorphism of completions `L_w ≃ L_{w'}` induced by `σ`. -/
theorem semilocalEquiv_semilocalGaloisHom (σ : L ≃ₐ[K] L)
    {w w' : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}}
    (h : w'.1.asIdeal = σ • w.1.asIdeal) (z : v.adicCompletion K ⊗[K] L) :
    semilocalEquiv L v (semilocalGaloisHom (v.adicCompletion K) L σ z) w' =
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
  Rep.res (semilocalGaloisHom (v.adicCompletion K) L)
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
      semilocalEquiv L v (semilocalGaloisHom (v.adicCompletion K) L g y) ⟨w, ‹_›⟩ :=
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

/-- For `L/K` Galois, `semilocalUnitsToCoind` is bijective: the semi-local units are the product
of the units of the completions above `v`, which `id ⊗ g` permutes through `completionCongr`. -/
private theorem semilocalUnitsToCoind_bijective [IsGalois K L] :
    Function.Bijective (semilocalUnitsToCoind v w).hom := by
  let e := ((Units.mapEquiv (semilocalEquiv L v).toMulEquiv).trans MulEquiv.piUnits).toEquiv
  let T (g : L ≃ₐ[K] L) {i j : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}}
      (h : j.1.asIdeal = g • i.1.asIdeal) :=
    (Units.mapEquiv (completionCongr v g h).toMulEquiv).toEquiv
  have he (g : L ≃ₐ[K] L) (y : (v.adicCompletion K ⊗[K] L)ˣ)
      {i j : {w : HeightOneSpectrum (𝒪 L) // w.asIdeal.LiesOver v.asIdeal}}
      (h : j.1.asIdeal = g • i.1.asIdeal) :
      e (Units.map (semilocalGaloisHom (v.adicCompletion K) L g : _ →* _) y) j = T g h (e y i) :=
    Units.ext (semilocalEquiv_semilocalGaloisHom g h y)
  refine ⟨fun y y' h ↦ Additive.toMul.injective <| semilocal_eq_of_forall_component_eq e T he
    (w := ⟨w, ‹_›⟩) (exists_asIdeal_eq_smul v w) fun g ↦ Units.ext ?_, fun F ↦ ?_⟩
  · exact (semilocalUnitsToCoind_apply v w y.toMul g).symm.trans <|
      (congrArg (fun F ↦ ((Additive.toMul (α := (w.adicCompletion L)ˣ) (F.1 g) :
        (w.adicCompletion L)ˣ) : w.adicCompletion L)) h).trans
          (semilocalUnitsToCoind_apply v w y'.toMul g)
  obtain ⟨y, hy⟩ := semilocal_exists_forall_component_eq e T he (w := ⟨w, ‹_›⟩)
    (fun g g' _ _ _ h h' a ↦
      Units.ext (DFunLike.congr_fun (completionCongr_trans (v := v) g g' h h') a.1))
    (exists_asIdeal_eq_smul v w) (exists_place_asIdeal_eq_smul v w)
    (fun g ↦ Additive.toMul (F.1 g)) fun d hd g ↦
      (congrArg Additive.toMul (F.2 ⟨d, MulAction.mem_stabilizer_iff.mpr hd.symm⟩ g)).trans <|
        Units.ext (DFunLike.congr_fun (decompositionHom_apply (v := v) (w := w)
          ⟨d, MulAction.mem_stabilizer_iff.mpr hd.symm⟩)
          (Additive.toMul (α := (w.adicCompletion L)ˣ) (F.1 g)).1)
  exact ⟨Additive.ofMul y, Subtype.ext <| funext fun g ↦ Additive.toMul.injective <|
    Units.ext <| (semilocalUnitsToCoind_apply v w y g).trans (congrArg Units.val (hy g))⟩

/-- **The semi-local units are coinduced.** For `L/K` Galois and `w` a place above `v`, the units
of `K_v ⊗[K] L` are, as an integral representation of `Gal(L/K)`, coinduced from the units of
`L_w` as a representation of the decomposition group of `w`. -/
def semilocalUnitsCoindIso [IsGalois K L] :
    semilocalUnitsRep L v ≅
      Rep.coind (MulAction.stabilizer (L ≃ₐ[K] L) w.asIdeal).subtype (decompositionUnitsRep v w) :=
  Rep.mkIso ((semilocalUnitsToCoind v w).hom.ofBijective
    (semilocalUnitsToCoind_bijective v w))

/-- The coinduction isomorphism is `semilocalUnitsToCoind`. -/
@[simp]
theorem semilocalUnitsCoindIso_hom [IsGalois K L] :
    (semilocalUnitsCoindIso v w).hom = semilocalUnitsToCoind v w :=
  (rfl)

end Coinduction

end TauCeti
