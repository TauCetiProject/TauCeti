/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra

/-!
# Base change of Hopf–Galois extensions

Let `H` be an `R`-bialgebra and `A` a commutative `H`-comodule algebra, with an `R`-algebra `B`
acting on `A` by coinvariants, so that `G = Spec H` acts on `X = Spec A` over `Y = Spec B`. For a
`B`-algebra `B'`, the base change `X ×_Y Y' = Spec (B' ⊗[B] A)` carries the induced action of `G`:
the coaction of `B' ⊗[B] A` is `b' ⊗ a ↦ b' ⊗ coact(a)`, read in
`B' ⊗[B] (A ⊗[R] H) ≃ (B' ⊗[B] A) ⊗[R] H` (`TauCeti.ComoduleAlgebra.baseChange`). The algebra `B'`
acts on it by coinvariants.

The Galois map of the base change is the base change of the Galois map: under the canonical
isomorphisms

  `(B' ⊗[B] A) ⊗[B'] (B' ⊗[B] A) ≃ B' ⊗[B] (A ⊗[B] A)` and
  `(B' ⊗[B] A) ⊗[R] H ≃ B' ⊗[B] (A ⊗[R] H)`,

it becomes `B' ⊗[B] β` (`TauCeti.ComoduleAlgebra.assoc_comp_galoisMap_baseChange`). Hence the
Galois property is stable under base change, and it descends along faithfully flat base change:
if `B'` is faithfully flat over `B`, then the Galois map of `A` over `B` is injective, surjective
or bijective exactly when that of `B' ⊗[B] A` over `B'` is. Geometrically, the isomorphism
`X × G ≅ X ×_Y X` which makes a faithfully flat `X ⟶ Y` a `G`-torsor can be checked after a
faithfully flat base change `Y' ⟶ Y`. Over any base `Y'`, the trivial torsor `Y' × G` has
bijective Galois map (`TauCeti.ComoduleAlgebra.galoisMap_baseChange_self_bijective`).

## Main definitions

* `TauCeti.ComoduleAlgebra.baseChangeCoact`: the coaction `B' ⊗[B] A → (B' ⊗[B] A) ⊗[R] H`, as a
  `B'`-algebra homomorphism.
* `TauCeti.ComoduleAlgebra.baseChange`: the comodule algebra structure on `B' ⊗[B] A`, selected
  explicitly as a local instance.

## Main results

* `TauCeti.ComoduleAlgebra.algebraMap_mem_coinvariants_baseChange`: `B'` acts on `B' ⊗[B] A` by
  coinvariants.
* `TauCeti.ComoduleAlgebra.assoc_comp_galoisMap_baseChange`: the Galois map of the base change is
  the base change of the Galois map.
* `TauCeti.ComoduleAlgebra.galoisMap_baseChange_bijective`: base change preserves bijectivity of
  the Galois map; `galoisMap_baseChange_surjective` and, for flat `B'`,
  `galoisMap_baseChange_injective` are the one-sided forms.
* `TauCeti.ComoduleAlgebra.galoisMap_baseChange_bijective_iff`: for faithfully flat `B'`, the
  Galois map is bijective if and only if that of the base change is; likewise
  `galoisMap_baseChange_injective_iff` and `galoisMap_baseChange_surjective_iff`.
* `TauCeti.ComoduleAlgebra.galoisMap_baseChange_self_bijective`: for a commutative Hopf algebra
  `H`, the trivial torsor `B' ⊗[R] H` over any `R`-algebra `B'` has bijective Galois map.

## References

* H. F. Kreimer and M. Takeuchi, *Hopf algebras and Galois extensions of an algebra*, Indiana Univ.
  Math. J. **30** (1981), 675–692.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, AMS, 1993, §8.1.
* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé IV, §5.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

universe u v w x y

section Semiring

variable {R : Type u} {H : Type v} {A : Type w} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [CommSemiring A] [Algebra R A] [ComoduleAlgebra R H A]
  {B : Type x} [CommSemiring B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
  (B' : Type y) [CommSemiring B'] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']

/-- The coaction of the base change `B' ⊗[B] A` of a comodule algebra along `B → B'`, for an
algebra `B` acting by coinvariants: `b' ⊗ a ↦ b' ⊗ coact(a)`, read in
`(B' ⊗[B] A) ⊗[R] H ≃ B' ⊗[B] (A ⊗[R] H)`. -/
noncomputable def baseChangeCoact (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    B' ⊗[B] A →ₐ[B'] (B' ⊗[B] A) ⊗[R] H :=
  (Algebra.TensorProduct.assoc R B B' B' A H).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id B' B') (coactAlgHomOver B hB))

variable {B'}

@[simp]
theorem baseChangeCoact_tmul (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) (b' : B')
    (a : A) :
    baseChangeCoact B' hB (b' ⊗ₜ a) =
      (Algebra.TensorProduct.assoc R B B' B' A H).symm
        (b' ⊗ₜ Comodule.coact (R := R) (C := H) a) := by
  simp [baseChangeCoact]

/-- On `b' ⊗ a`, the base-changed coaction is the coaction of `a` pushed forward along
`a ↦ b' ⊗ a`. -/
theorem baseChangeCoact_tmul_eq_rTensor (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (b' : B') (a : A) :
    baseChangeCoact B' hB (b' ⊗ₜ a) =
      ((TensorProduct.mk B B' A b').restrictScalars R).rTensor H
        (Comodule.coact (R := R) (C := H) a) := by
  rw [baseChangeCoact_tmul]
  induction Comodule.coact (R := R) (C := H) a with
  | tmul x h => simp
  | add s t hs ht => simp [TensorProduct.tmul_add, hs, ht]

/-- The base-changed coaction intertwines `a ↦ b' ⊗ a` with the coaction of `A`. -/
private theorem baseChangeCoact_comp_mk (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (b' : B') :
    ((baseChangeCoact B' hB).restrictScalars R).toLinearMap ∘ₗ
        (TensorProduct.mk B B' A b').restrictScalars R =
      ((TensorProduct.mk B B' A b').restrictScalars R).rTensor H ∘ₗ
        Comodule.coact (R := R) (C := H) (M := A) :=
  LinearMap.ext fun a ↦ baseChangeCoact_tmul_eq_rTensor hB b' a

variable (B') in
/-- The **base change** of a comodule algebra `A` along `B → B'`, for an algebra `B` acting on `A`
by coinvariants: the comodule algebra `B' ⊗[B] A`, whose coaction is
`TauCeti.ComoduleAlgebra.baseChangeCoact`. It is the action of `Spec H` on
`Spec A ×_{Spec B} Spec B'`. It depends on `B`, so it is not a global instance. -/
noncomputable abbrev baseChange (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    ComoduleAlgebra R H (B' ⊗[B] A) where
  coact := ((baseChangeCoact B' hB).restrictScalars R).toLinearMap
  coassoc := by
    refine LinearMap.ext fun x ↦ ?_
    induction x with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b' a =>
      set φ := (TensorProduct.mk B B' A b').restrictScalars R
      set ρ' := ((baseChangeCoact B' hB).restrictScalars R).toLinearMap
      have hφ : ∀ t, ρ'.rTensor H (φ.rTensor H t) =
          (φ.rTensor H).rTensor H ((Comodule.coact (R := R) (C := H) (M := A)).rTensor H t) := by
        intro t
        rw [← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply]
        exact congrArg (fun f ↦ f.rTensor H t) (baseChangeCoact_comp_mk hB b')
      have hassoc : ∀ s, TensorProduct.assoc R (B' ⊗[B] A) H H ((φ.rTensor H).rTensor H s) =
          φ.rTensor (H ⊗[R] H) (TensorProduct.assoc R A H H s) := by
        intro s
        simpa [LinearMap.rTensor, TensorProduct.map_id] using
          (TensorProduct.map_map_assoc φ LinearMap.id LinearMap.id s).symm
      have hcomm : ∀ u, φ.rTensor (H ⊗[R] H) (Coalgebra.comul.lTensor A u) =
          Coalgebra.comul.lTensor (B' ⊗[B] A) (φ.rTensor H u) := by
        intro u
        rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.comp_apply,
          LinearMap.lTensor_comp_rTensor]
      have key := LinearMap.congr_fun (Comodule.coassoc (R := R) (C := H) (M := A)) a
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at key ⊢
      have hρ : ρ' (b' ⊗ₜ a) = φ.rTensor H (Comodule.coact (R := R) (C := H) a) :=
        baseChangeCoact_tmul_eq_rTensor hB b' a
      rw [hρ, hφ, hassoc, key, hcomm]
  lTensor_counit_comp_coact := by
    refine LinearMap.ext fun x ↦ ?_
    induction x with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b' a =>
      set φ := (TensorProduct.mk B B' A b').restrictScalars R
      have key := LinearMap.congr_fun (Comodule.lTensor_counit_comp_coact (R := R) (C := H)
        (M := A)) a
      have hcomm : ∀ u, Coalgebra.counit.lTensor (B' ⊗[B] A) (φ.rTensor H u) =
          φ.rTensor R (Coalgebra.counit.lTensor A u) := by
        intro u
        rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, ← LinearMap.comp_apply,
          LinearMap.rTensor_comp_lTensor]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply] at key ⊢
      rw [AlgHom.toLinearMap_apply, AlgHom.coe_restrictScalars', baseChangeCoact_tmul_eq_rTensor,
        hcomm, key]
      simp [φ]
  coact_one := map_one (baseChangeCoact B' hB)
  coact_mul := map_mul (baseChangeCoact B' hB)

/-- On the base change `B' ⊗[B] A`, the coaction is `TauCeti.ComoduleAlgebra.baseChangeCoact`. -/
@[simp]
theorem coact_baseChange (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) (x : B' ⊗[B] A) :
    letI := baseChange B' hB
    Comodule.coact (R := R) (C := H) x = baseChangeCoact B' hB x :=
  (rfl)

/-- The algebra `B'` acts on the base change `B' ⊗[B] A` by coinvariants. -/
theorem algebraMap_mem_coinvariants_baseChange
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) (b' : B') :
    letI := baseChange B' hB
    algebraMap B' (B' ⊗[B] A) b' ∈ coinvariants R H (B' ⊗[B] A) := by
  let := baseChange B' hB
  rw [mem_coinvariants, coact_baseChange, AlgHom.commutes,
    Algebra.TensorProduct.algebraMap_apply]

variable (B')

/-- **The Galois map of a base change is the base change of the Galois map.** Under the
isomorphisms `(B' ⊗[B] A) ⊗[B'] (B' ⊗[B] A) ≃ B' ⊗[B] (A ⊗[B] A)` and
`(B' ⊗[B] A) ⊗[R] H ≃ B' ⊗[B] (A ⊗[R] H)`, the Galois map of `B' ⊗[B] A` over `B'` is
`B' ⊗[B] β`, where `β` is the Galois map of `A` over `B`. -/
theorem assoc_comp_galoisMap_baseChange (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    letI := baseChange B' hB
    (Algebra.TensorProduct.assoc R B B' B' A H).toAlgHom.comp
        ((galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)).restrictScalars B') =
      (Algebra.TensorProduct.map (AlgHom.id B' B') ((galoisMap B hB).restrictScalars B)).comp
        ((Algebra.TensorProduct.cancelBaseChange B B' B' (B' ⊗[B] A) A).trans
          (Algebra.TensorProduct.assoc B B B' B' A A)).toAlgHom := by
  let := baseChange B' hB
  ext a
  · simp [Algebra.TensorProduct.one_def]
  · simp [Algebra.TensorProduct.one_def]

/-- As a function, the Galois map of `B' ⊗[B] A` over `B'` is `B' ⊗[B] β` between the canonical
isomorphisms, where `β` is the Galois map of `A` over `B`. -/
private theorem coe_galoisMap_baseChange (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    letI := baseChange B' hB
    ⇑(galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) =
      (Algebra.TensorProduct.assoc R B B' B' A H).symm ∘
        LinearMap.lTensor B' ((galoisMap B hB).restrictScalars B).toLinearMap ∘
          (Algebra.TensorProduct.cancelBaseChange B B' B' (B' ⊗[B] A) A).trans
            (Algebra.TensorProduct.assoc B B B' B' A A) := by
  let := baseChange B' hB
  have hmap : ⇑(Algebra.TensorProduct.map (AlgHom.id B' B') ((galoisMap B hB).restrictScalars B)) =
      LinearMap.lTensor B' ((galoisMap B hB).restrictScalars B).toLinearMap := by
    funext x
    induction x with
    | tmul b' y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  funext x
  have h := AlgHom.congr_fun (assoc_comp_galoisMap_baseChange B' hB) x
  simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, AlgHom.coe_restrictScalars',
    Function.comp_apply, hmap] at h
  simp only [Function.comp_apply, ← h, AlgEquiv.symm_apply_apply]

/-- Base change preserves surjectivity of the Galois map. -/
theorem galoisMap_baseChange_surjective (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (h : Function.Surjective (galoisMap B hB)) :
    letI := baseChange B' hB
    Function.Surjective (galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) := by
  let := baseChange B' hB
  rw [coe_galoisMap_baseChange, EquivLike.comp_surjective, EquivLike.surjective_comp]
  exact LinearMap.lTensor_surjective B' (by simpa using h)

/-- **Base change of a Hopf–Galois extension.** Base change preserves bijectivity of the Galois
map: if `Spec A × Spec H ⟶ Spec A ×_{Spec B} Spec A` is an isomorphism, so is its base change
along any `Spec B' ⟶ Spec B`. -/
theorem galoisMap_baseChange_bijective (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (h : Function.Bijective (galoisMap B hB)) :
    letI := baseChange B' hB
    Function.Bijective (galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) := by
  let := baseChange B' hB
  rw [coe_galoisMap_baseChange, EquivLike.comp_bijective, EquivLike.bijective_comp]
  exact (LinearEquiv.ofBijective (((galoisMap B hB).restrictScalars B).toLinearMap)
    (by simpa using h)).lTensor B' |>.bijective

/-- **The trivial torsor over any base.** For a commutative Hopf algebra `H` over `R` and an
`R`-algebra `B'`, the base change `B' ⊗[R] H` of the regular comodule algebra has bijective Galois
map over `B'`: the action of `Spec H` on `Spec B' × Spec H` by right translation on the second
factor makes it a torsor over `Spec B'` as soon as it is faithfully flat. -/
theorem galoisMap_baseChange_self_bijective {R : Type u} {H : Type v} [CommSemiring R]
    [CommSemiring H] [HopfAlgebra R H] (B' : Type y) [CommSemiring B'] [Algebra R B'] :
    letI := baseChange B' fun r ↦ (coinvariants R H H).algebraMap_mem r
    Function.Bijective (galoisMap B' (algebraMap_mem_coinvariants_baseChange
      fun r ↦ (coinvariants R H H).algebraMap_mem r)) :=
  galoisMap_baseChange_bijective B' _ galoisMap_self_bijective

end Semiring

section Ring

variable {R : Type u} {H : Type v} {A : Type w} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [CommRing A] [Algebra R A] [ComoduleAlgebra R H A]
  {B : Type x} [CommRing B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
  (B' : Type y) [CommRing B'] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']

/-- Flat base change preserves injectivity of the Galois map. -/
theorem galoisMap_baseChange_injective [Module.Flat B B']
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (h : Function.Injective (galoisMap B hB)) :
    letI := baseChange B' hB
    Function.Injective (galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) := by
  let := baseChange B' hB
  rw [coe_galoisMap_baseChange, EquivLike.comp_injective, EquivLike.injective_comp]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (by simpa using h)

variable [Module.FaithfullyFlat B B']

/-- **Faithfully flat descent of injectivity of the Galois map.** For faithfully flat `B'` over
`B`, the Galois map of `A` over `B` is injective if and only if that of `B' ⊗[B] A` over `B'`
is. -/
theorem galoisMap_baseChange_injective_iff
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    letI := baseChange B' hB
    Function.Injective (galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) ↔
      Function.Injective (galoisMap B hB) := by
  let := baseChange B' hB
  rw [coe_galoisMap_baseChange, EquivLike.comp_injective, EquivLike.injective_comp,
    Module.FaithfullyFlat.lTensor_injective_iff_injective, AlgHom.coe_toLinearMap,
    AlgHom.coe_restrictScalars']

/-- **Faithfully flat descent of surjectivity of the Galois map.** For faithfully flat `B'` over
`B`, the Galois map of `A` over `B` is surjective if and only if that of `B' ⊗[B] A` over `B'`
is. -/
theorem galoisMap_baseChange_surjective_iff
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    letI := baseChange B' hB
    Function.Surjective (galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) ↔
      Function.Surjective (galoisMap B hB) := by
  let := baseChange B' hB
  rw [coe_galoisMap_baseChange, EquivLike.comp_surjective, EquivLike.surjective_comp,
    Module.FaithfullyFlat.lTensor_surjective_iff_surjective, AlgHom.coe_toLinearMap,
    AlgHom.coe_restrictScalars']

/-- **Faithfully flat descent of the Galois property.** For faithfully flat `B'` over `B`, the
Galois map of `A` over `B` is bijective if and only if that of `B' ⊗[B] A` over `B'` is: the
isomorphism `Spec A × Spec H ≅ Spec A ×_{Spec B} Spec A` of a torsor can be checked after the
faithfully flat base change `Spec B' ⟶ Spec B`. -/
theorem galoisMap_baseChange_bijective_iff
    (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A) :
    letI := baseChange B' hB
    Function.Bijective (galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) ↔
      Function.Bijective (galoisMap B hB) := by
  let := baseChange B' hB
  rw [Function.Bijective, Function.Bijective, galoisMap_baseChange_injective_iff,
    galoisMap_baseChange_surjective_iff]

end Ring

end TauCeti.ComoduleAlgebra
