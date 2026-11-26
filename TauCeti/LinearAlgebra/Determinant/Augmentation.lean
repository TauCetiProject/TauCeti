/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Comp.Basic
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.Prod

/-!
# The determinant line of a map augmented by finitely many linear conditions

Let `f : M → N` be a linear map with finite-dimensional kernel and cokernel, and let
`g : M → V` be a linear map to a finite-dimensional space. The **augmented map**
`f.prod g : M → N × V`, `m ↦ (f m, g m)`, imposes the finitely many conditions `g` in addition to
`f`. Since `f` is the composite of `f.prod g` with the projection `N × V → N`, the composition law
of determinant lines (`LinearMap.detLineCompEquiv`) relates the determinant lines
`det f = det (ker f) ⊗ (det (coker f))^*` of the two maps. The projection is onto with kernel
`0 × V`, so its determinant line is `det V` (`LinearMap.detLineFstEquiv`), and this gives the
canonical isomorphism

`det f ≃ det (f.prod g) ⊗ det V`

(`LinearMap.detLineEquivProd`). Since `det V` is a line, orientations of any two of `det f`,
`det (f.prod g)` and `V` orient the third.

The typical instance is a Fredholm operator `f`, the linearization of a moduli problem, augmented by
the evaluation `g` of its sections at finitely many points, with `V` the sum of the fibres at
these points. The kernel of `f.prod g` is then the tangent space of the moduli space cut down by
the point constraints. When `f.prod g` is bijective, `g` maps the kernel of `f` isomorphically
onto `V` and `f` is onto, and the isomorphism becomes `det f ≃ det V`
(`LinearMap.detLineEquivOfBijectiveProd`): it sends `u₁ ∧ ⋯ ∧ uₙ ⊗ φ` to `g u₁ ∧ ⋯ ∧ g uₙ`, up
to the value of `φ` on the generator of the zero cokernel
(`LinearMap.coe_detLineEquivOfBijectiveProd_tmul`). Comparing an orientation of `det f` with an
orientation of `V` through it is the sign with which a point of the cut-down moduli space is
counted.

## Main declarations

* `LinearMap.detLineFstEquiv`: the determinant line of the projection `N × V → N` is `det V`.
* `LinearMap.detLineEquivProd`: the isomorphism `det f ≃ det (f.prod g) ⊗ det V`.
* `LinearMap.detLineEquivOfBijectiveProd`: for bijective `f.prod g`, the isomorphism
  `det f ≃ det V`, with its value `LinearMap.coe_detLineEquivOfBijectiveProd_tmul`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential
  Geom. **44** (1996), 818–893 (orientations of curves through fixed points).
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

variable {K : Type*} [Field K] {M N V : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] [AddCommGroup V] [Module K V]

/-! ### The projection `N × V → N` -/

section Fst

variable (K N V)

private theorem finrank_quotient_range_fst : finrank K (N ⧸ range (fst K N V)) = 0 :=
  finrank_quotient_range_eq_zero_of_surjective Prod.fst_surjective

-- `ker (fst K N V)` is `Submodule.snd K N V` by definition.
instance [FiniteDimensional K V] : FiniteDimensional K (ker (fst K N V)) :=
  (Submodule.sndEquiv K N V).symm.finiteDimensional

instance : FiniteDimensional K (N ⧸ range (fst K N V)) :=
  have : Subsingleton (N ⧸ range (fst K N V)) :=
    Submodule.Quotient.subsingleton_iff.mpr (range_eq_top.mpr Prod.fst_surjective)
  inferInstance

/-- **The determinant line of the projection `N × V → N` is `det V`.** The projection is onto, so
its cokernel is zero, and its kernel `0 × V`, which is `Submodule.snd K N V`, is identified with
`V` by the second projection (`Submodule.sndEquiv`). The isomorphism sends `w ⊗ φ` to the image of
`w` in `det V`, multiplied by the value of `φ` on the empty exterior product of the cokernel
(`LinearMap.coe_detLineFstEquiv_tmul`). -/
def detLineFstEquiv : (fst K N V).detLine ≃ₗ[K] TauCeti.detLine K V :=
  TensorProduct.congr (LinearEquiv.detLineCongr (LinearEquiv.ofEq (ker (fst K N V))
      (Submodule.snd K N V) (Submodule.ext fun _ ↦ Iff.rfl) ≪≫ₗ Submodule.sndEquiv K N V))
      ((TauCeti.detLineEquivOfFinrankEqZero (finrank_quotient_range_fst K N V)).symm.dualMap ≪≫ₗ
        ringLmapEquivSelf K K K) ≪≫ₗ
    TensorProduct.rid K _

variable {K N V} in
/-- **The value of `LinearMap.detLineFstEquiv`.** The exterior product of a family `w` in the
kernel `0 × V` of the projection, tensored with `φ`, goes to the exterior product of the second
components of `w`, multiplied by the value of `φ` on the empty exterior product `e` of the zero
cokernel. -/
theorem coe_detLineFstEquiv_tmul (w : Fin (finrank K (ker (fst K N V))) → ker (fst K N V))
    (φ : Dual K (TauCeti.detLine K (N ⧸ range (fst K N V))))
    (e : Fin (finrank K (N ⧸ range (fst K N V))) → N ⧸ range (fst K N V)) :
    (detLineFstEquiv K N V (exteriorPower.ιMulti K _ w ⊗ₜ φ) : ExteriorAlgebra K V) =
      φ (exteriorPower.ιMulti K _ e) • ExteriorAlgebra.ιMulti K _ fun i ↦ (w i : N × V).2 := by
  have he : e = Fin.elim0 ∘ Fin.cast (finrank_quotient_range_fst K N V) :=
    funext fun i ↦ (Fin.cast (finrank_quotient_range_fst K N V) i).elim0
  rw [detLineFstEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul, TensorProduct.rid_tmul,
    LinearEquiv.detLineCongr_ιMulti, SetLike.val_smul, exteriorPower.ιMulti_apply_coe,
    ← Function.comp_assoc, TauCeti.ExteriorAlgebra.ιMulti_comp_cast, he]
  simp [ringLmapEquivSelf_apply, Function.comp_def]

end Fst

/-! ### The augmented map `f.prod g` -/

section Prod

variable (f : M →ₗ[K] N) (g : M →ₗ[K] V)

instance [FiniteDimensional K (ker f)] : FiniteDimensional K (ker (f.prod g)) :=
  Module.Finite.of_injective _ (Submodule.inclusion_injective ((ker_prod f g).trans_le inf_le_left))

instance [FiniteDimensional K V] [FiniteDimensional K (N ⧸ range f)] :
    FiniteDimensional K ((N × V) ⧸ range (f.prod g)) :=
  -- `coker (f.prod g)` sits between `ker (fst)`, a copy of `V`, and `coker (fst ∘ₗ f.prod g)`,
  -- which is `coker f` since `fst ∘ₗ f.prod g = f`.
  have : FiniteDimensional K (N ⧸ range (fst K N V ∘ₗ f.prod g)) := by
    rw [fst_prod]
    infer_instance
  ((f.prod g).exact_kerToCoker_cokerToCokerComp (fst K N V)).moduleFinite

variable [FiniteDimensional K V] [FiniteDimensional K (ker f)] [FiniteDimensional K (N ⧸ range f)]

/-- **The determinant line of an augmented map.** For `f : M → N` with finite-dimensional kernel
and cokernel and `g : M → V` with `V` finite-dimensional, the canonical isomorphism

`det f ≃ det (f.prod g) ⊗ det V`.

It is the composition law `LinearMap.detLineCompEquiv` for `f = fst ∘ (f.prod g)`, followed by the
identification `LinearMap.detLineFstEquiv` of the determinant line of the projection
`fst : N × V → N` with `det V` (`LinearMap.detLineEquivProd_def`). -/
def detLineEquivProd : f.detLine ≃ₗ[K] (f.prod g).detLine ⊗[K] TauCeti.detLine K V :=
  -- `fst ∘ₗ f.prod g` is `f` by definition: `LinearMap.fst_prod` is proved by `rfl`.
  (f.prod g).detLineCompEquiv (fst K N V) ≪≫ₗ
    TensorProduct.congr (LinearEquiv.refl K _) (detLineFstEquiv K N V)

theorem detLineEquivProd_def :
    f.detLineEquivProd g = (f.prod g).detLineCompEquiv (fst K N V) ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl K _) (detLineFstEquiv K N V) :=
  (rfl)

end Prod

/-! ### Bijective augmented maps -/

section Bijective

variable (f : M →ₗ[K] N) (g : M →ₗ[K] V)

/-- **The determinant line of a bijective augmented map.** When `f.prod g` is bijective, its
determinant line is `K` (`LinearMap.detLineEquivOfBijective`), and `LinearMap.detLineEquivProd`
becomes an isomorphism `det f ≃ det V`. In this case `g` maps the kernel of `f` isomorphically
onto `V` and `f` is onto, so the kernel and cokernel of `f` are finite-dimensional, and the
isomorphism sends `u₁ ∧ ⋯ ∧ uₙ ⊗ φ` to `g u₁ ∧ ⋯ ∧ g uₙ` up to the value of `φ` on the generator of
the zero cokernel (`LinearMap.coe_detLineEquivOfBijectiveProd_tmul`). -/
def detLineEquivOfBijectiveProd [FiniteDimensional K V] (h : Function.Bijective (f.prod g)) :
    f.detLine ≃ₗ[K] TauCeti.detLine K V :=
  have := finite_ker_of_injective_prod h.1
  have := subsingleton_quotient_range_of_surjective_prod h.2
  f.detLineEquivProd g ≪≫ₗ
    TensorProduct.congr (detLineEquivOfBijective h) (LinearEquiv.refl K _) ≪≫ₗ
    TensorProduct.lid K _

/-- The computation behind `LinearMap.coe_detLineEquivOfBijectiveProd_tmul`, for a bijective map
`F : M → N × V` and the composite `fst ∘ₗ F`, which for `F = f.prod g` is `f`. -/
private theorem coe_lid_detLineCompEquiv_fst_tmul (F : M →ₗ[K] N × V) [FiniteDimensional K V]
    [FiniteDimensional K (ker F)] [FiniteDimensional K ((N × V) ⧸ range F)]
    (h : Function.Bijective F) (u : Fin (finrank K (ker (fst K N V ∘ₗ F))) → ker (fst K N V ∘ₗ F))
    (φ : Dual K (TauCeti.detLine K (N ⧸ range (fst K N V ∘ₗ F))))
    (e : Fin (finrank K (N ⧸ range (fst K N V ∘ₗ F))) → N ⧸ range (fst K N V ∘ₗ F)) :
    (TensorProduct.lid K (TauCeti.detLine K V) (TensorProduct.congr (detLineEquivOfBijective h)
        (LinearEquiv.refl K _) (TensorProduct.congr (LinearEquiv.refl K _) (detLineFstEquiv K N V)
          (F.detLineCompEquiv (fst K N V) (exteriorPower.ιMulti K _ u ⊗ₜ φ)))) :
        ExteriorAlgebra K V) =
      φ (exteriorPower.ιMulti K _ e) • ExteriorAlgebra.ιMulti K _ fun i ↦ (F (u i)).2 := by
  -- `F` is bijective, so `ker (fst ∘ₗ F) → ker fst` is injective and the other families of
  -- `LinearMap.detLineCompEquiv_tmul` are empty.
  have h₀ := finrank_quotient_range_fst K N V
  have hker : finrank K (ker F) = 0 := finrank_ker_eq_zero_of_injective h.1
  have hcoker : finrank K ((N × V) ⧸ range F) = 0 :=
    finrank_quotient_range_eq_zero_of_surjective h.2
  have hcf : finrank K (N ⧸ range (fst K N V ∘ₗ F)) = 0 :=
    finrank_quotient_range_eq_zero_of_surjective (Prod.fst_surjective.comp h.2)
  have hv : finrank K (range (F.kerCompToKer (fst K N V))) = finrank K (ker (fst K N V ∘ₗ F)) :=
    finrank_range_of_inj fun x y hxy ↦ Subtype.ext (h.1 (by simpa using congrArg Subtype.val hxy))
  have hw : finrank K (range (F.kerToCoker (fst K N V))) = 0 :=
    Nat.le_zero.mp ((Submodule.finrank_le _).trans_eq hcoker)
  have hx : finrank K (range (F.cokerToCokerComp (fst K N V))) = 0 :=
    Nat.le_zero.mp ((finrank_range_le _).trans_eq hcoker)
  have hK : finrank K (ker (fst K N V)) = finrank K (range (F.kerCompToKer (fst K N V))) +
      finrank K (range (F.kerToCoker (fst K N V))) :=
    finrank_eq_finrank_range_add_finrank_range_of_exact _ _
      (F.exact_kerCompToKer_kerToCoker (fst K N V))
  have hK' : finrank K (ker (fst K N V)) = finrank K (ker (fst K N V ∘ₗ F)) := by
    rw [hK, hw, add_zero, hv]
  let w : Fin _ → ker (fst K N V) := Fin.elim0 ∘ Fin.cast hw
  let a := F.kerCompToKer (fst K N V) ∘ u ∘ Fin.cast hK'
  rw [F.detLineCompEquiv_tmul (fst K N V) (Fin.elim0 ∘ Fin.cast hker) (u ∘ Fin.cast hv) w
      (Fin.elim0 ∘ Fin.cast hx) (Fin.elim0 ∘ Fin.cast h₀)
      (β := exteriorPower.ιMulti K _ u) ?_ (γ := exteriorPower.ιMulti K _ a) ?_
      (δ := exteriorPower.ιMulti K _ (Fin.elim0 ∘ Fin.cast hcoker)) ?_
      (ε := exteriorPower.ιMulti K _ e) ?_ φ
      (ψ := (TauCeti.detLineEquivOfFinrankEqZero hcoker :
        TauCeti.detLine K ((N × V) ⧸ range F) →ₗ[K] K)) (by simp)
      (χ := (TauCeti.detLineEquivOfFinrankEqZero h₀ :
        TauCeti.detLine K (N ⧸ range (fst K N V)) →ₗ[K] K)) (by simp)]
  · simp only [map_smul, TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.lid_tmul,
      SetLike.val_smul, detLineEquivOfBijective_tmul_ιMulti h _ _ (Fin.elim0 ∘ Fin.cast hcoker),
      LinearEquiv.coe_coe, TauCeti.detLineEquivOfFinrankEqZero_ιMulti, one_smul,
      coe_detLineFstEquiv_tmul _ _ (Fin.elim0 ∘ Fin.cast h₀)]
    -- The second components of `a` are those of `F ∘ u`.
    have ha : (fun i ↦ (a i : N × V).2) = (fun i ↦ (F (u i)).2) ∘ Fin.cast hK' :=
      funext fun i ↦ congrArg Prod.snd (coe_kerCompToKer_apply F (fst K N V) _)
    rw [ha, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  · rw [exteriorPower.ιMulti_apply_coe,
      TauCeti.ExteriorAlgebra.ιMulti_append_of_eq_zero_left hker,
      TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  · rw [exteriorPower.ιMulti_apply_coe,
      TauCeti.ExteriorAlgebra.ιMulti_append_of_eq_zero_right hw]
    simp only [a, ← Function.comp_assoc, TauCeti.ExteriorAlgebra.ιMulti_comp_cast]
  · rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero hcoker,
      TauCeti.ExteriorAlgebra.ιMulti_append_of_eq_zero_left hw,
      TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero hx]
  · rw [exteriorPower.ιMulti_apply_coe, TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero hcf,
      TauCeti.ExteriorAlgebra.ιMulti_append_of_eq_zero_left hx,
      TauCeti.ExteriorAlgebra.ιMulti_of_eq_zero h₀]

variable [FiniteDimensional K V]

/-- **The value of `LinearMap.detLineEquivOfBijectiveProd`.** For a family `u` of `dim (ker f)`
vectors of the kernel of `f`, the exterior product of `u` tensored with `φ` goes to the exterior
product of `g ∘ u` in `V`, multiplied by the value of `φ` on the empty exterior product `e` of the
zero cokernel of `f`. In particular, an orientation of `det f` and an orientation of `V` agree
exactly when, for a basis `u` of `ker f` positive for the first, `g ∘ u` is positive for the
second. -/
theorem coe_detLineEquivOfBijectiveProd_tmul (h : Function.Bijective (f.prod g))
    (u : Fin (finrank K (ker f)) → ker f) (φ : Dual K (TauCeti.detLine K (N ⧸ range f)))
    (e : Fin (finrank K (N ⧸ range f)) → N ⧸ range f) :
    (f.detLineEquivOfBijectiveProd g h (exteriorPower.ιMulti K _ u ⊗ₜ φ) :
        ExteriorAlgebra K V) =
      φ (exteriorPower.ιMulti K _ e) • ExteriorAlgebra.ιMulti K _ (g.domRestrict (ker f) ∘ u) :=
  have := finite_ker_of_injective_prod h.1
  have := subsingleton_quotient_range_of_surjective_prod h.2
  -- `fst ∘ₗ f.prod g` is `f` by definition (`LinearMap.fst_prod` is proved by `rfl`), and
  -- `((f.prod g) x).2` is `g x`.
  coe_lid_detLineCompEquiv_fst_tmul (f.prod g) h u φ e

end Bijective

end LinearMap
