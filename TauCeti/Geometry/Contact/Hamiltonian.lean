/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Flat
public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Contact Hamiltonian vector fields

Let `α` be a contact form on a finite-dimensional manifold `M`, with Reeb vector field `R_α`. The
**contact Hamiltonian vector field** of a function `f : M → ℝ`
(`TauCeti.SmoothForm.contactHamiltonianVectorField`) is the vector field `X_f` determined by

`α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df`.

It is obtained by inverting the contact flat map `v ↦ ι_v dα + α(v) α`
(`TauCeti.SmoothForm.contactFlat`) on the covector `(R_α f + f) α - df`. These two equations
determine `X_f` uniquely
(`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff`), and it is enough to test
the second one on the contact distribution `ξ = ker α`, where it reads `ι_(X_f) dα = -df`
(`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff_kerDistribution`).

By Cartan's formula `L_X α = ι_X dα + d(α(X))` (`TauCeti.mlieDerivForm_apply_one`), the defining
equations give, wherever `X_f` is differentiable,

`L_(X_f) α = (R_α f) α`

(`TauCeti.SmoothForm.IsContactForm.mlieDerivForm_contactHamiltonianVectorField_apply`, and
`TauCeti.SmoothForm.IsContactForm.mlieDerivForm_contactHamiltonianVectorField` for a `C²`
function `f`). This is the infinitesimal form of the classical fact, not formalized here, that the
local flow of `X_f` preserves `ξ` together with its coorientation. In particular, the bracket of
`X_f` with any vector field tangent to `ξ` near a point is tangent to `ξ` at that point
(`TauCeti.SmoothForm.IsContactForm.mlieBracket_contactHamiltonianVectorField_mem_kerDistribution`);
this holds for every vector field `V` with `L_V α` a multiple of `α` at the point
(`TauCeti.SmoothForm.mlieBracket_mem_kerDistribution_of_mlieDerivForm_eq_smul`).
Conversely, if a vector field `X` is differentiable at `x` and `(L_X α)_x` is a multiple of `α_x`,
then `X(x)` is the value at `x` of the contact Hamiltonian vector field of `α(X)`
(`TauCeti.SmoothForm.IsContactForm.exists_mlieDerivForm_eq_smul_iff`), and the factor is
`R_α(α(X))` at `x`
(`TauCeti.SmoothForm.IsContactForm.eq_mvfderiv_reebVectorField_of_mlieDerivForm_eq_smul`).

The Hamiltonian `f = 1` gives the Reeb vector field, and more generally a constant `c` gives
`c R_α` (`TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_const`). The field `X_f`
is tangent to `ξ` exactly where `f` vanishes. Unlike a symplectic Hamiltonian vector field,
`X_f` need not preserve `f`: one has `df(X_f) = (R_α f) f`
(`TauCeti.SmoothForm.IsContactForm.mvfderiv_apply_contactHamiltonianVectorField`). Since the Reeb
vector field is smooth (`TauCeti.SmoothForm.IsContactForm.contMDiff_reebVectorField`), the contact
Hamiltonian vector field of a `C^(n+1)` function is a `C^n` vector field
(`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField`).

## Conventions

This file follows the convention `α(X_f) = f`, `ι_(X_f) dα = (R_α f) α - df` of Geiges' book.
Some authors (for example in contact Hamiltonian mechanics) use the opposite sign
`α(X_f) = -f`, `ι_(X_f) dα = df - (R_α f) α`; their field for `f` is the field here for `-f`
(`TauCeti.SmoothForm.contactHamiltonianVectorField_neg`). Both conventions give the same
correspondence between the vector fields that preserve `ξ` and their Hamiltonians, up to this
sign.

## Main declarations

* `TauCeti.SmoothForm.contactHamiltonianVectorField`: the contact Hamiltonian vector field.
* `TauCeti.SmoothForm.IsContactForm.apply_contactHamiltonianVectorField`,
  `TauCeti.SmoothForm.IsContactForm.mextDeriv_contactHamiltonianVectorField_left`: the defining
  equations.
* `TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff`: uniqueness.
* `TauCeti.SmoothForm.IsContactForm.contactHamiltonianVectorField_const`: constant Hamiltonians
  give multiples of the Reeb vector field.
* `TauCeti.SmoothForm.IsContactForm.mlieDerivForm_contactHamiltonianVectorField_apply`: the Lie
  derivative `L_(X_f) α = (R_α f) α`.
* `TauCeti.SmoothForm.IsContactForm.exists_mlieDerivForm_eq_smul_iff`: at a point, the vector
  fields whose Lie derivative is a multiple of `α` are the contact Hamiltonian vector fields.
* `TauCeti.SmoothForm.mlieBracket_mem_kerDistribution_of_mlieDerivForm_eq_smul`,
  `TauCeti.SmoothForm.IsContactForm.mlieBracket_contactHamiltonianVectorField_mem_kerDistribution`:
  such vector fields, and in particular contact Hamiltonian vector fields, preserve `ξ`
  infinitesimally.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.3.
-/

public section

noncomputable section

open Bundle Module
open scoped ContDiff Manifold Topology

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α : SmoothForm I M ℝ 1} {f g : M → ℝ}

/-- The **contact Hamiltonian vector field** `X_f` of a function `f` for a one-form `α`: the
preimage of the covector `(R_α f + f) α - df` under the contact flat map `v ↦ ι_v dα + α(v) α`.
For a contact form on a finite-dimensional manifold it is the unique vector field with
`α(X_f) = f` and `ι_(X_f) dα = (R_α f) α - df`
(`TauCeti.SmoothForm.IsContactForm.eq_contactHamiltonianVectorField_iff`); the inverse is
`ContinuousLinearMap.inverse`, so the field vanishes at points where the contact flat map is not
invertible. -/
def contactHamiltonianVectorField (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    TangentSpace I x :=
  (α.contactFlat x).inverse
    ((mvfderiv I f x (α.reebVectorField x) + f x) • degreeOneEquiv α x - mvfderiv I f x)

/-- The contact Hamiltonian vector field unfolds as the inverse contact flat map applied to
`(R_α f + f) α - df`. -/
theorem contactHamiltonianVectorField_def (α : SmoothForm I M ℝ 1) (f : M → ℝ) (x : M) :
    α.contactHamiltonianVectorField f x = (α.contactFlat x).inverse
      ((mvfderiv I f x (α.reebVectorField x) + f x) • degreeOneEquiv α x - mvfderiv I f x) :=
  (rfl)

/-- The contact Hamiltonian vector field is additive on differentiable functions. -/
theorem contactHamiltonianVectorField_add {x : M} (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) :
    α.contactHamiltonianVectorField (f + g) x =
      α.contactHamiltonianVectorField f x + α.contactHamiltonianVectorField g x := by
  rw [contactHamiltonianVectorField_def, contactHamiltonianVectorField_def,
    contactHamiltonianVectorField_def, ← map_add, mvfderiv_add hf hg]
  congr 1
  simp only [add_apply, Pi.add_apply]
  module

/-- The contact Hamiltonian vector field commutes with multiplication by a real constant. -/
@[simp]
theorem contactHamiltonianVectorField_const_smul (c : ℝ) (x : M) :
    α.contactHamiltonianVectorField (c • f) x = c • α.contactHamiltonianVectorField f x := by
  rw [contactHamiltonianVectorField_def, contactHamiltonianVectorField_def, ← map_smul,
    mvfderiv_const_smul_of_field]
  congr 1
  simp only [smul_apply, Pi.smul_apply, smul_eq_mul]
  module

/-- The contact Hamiltonian vector field of `-f` is the opposite of that of `f`. -/
@[simp]
theorem contactHamiltonianVectorField_neg (x : M) :
    α.contactHamiltonianVectorField (-f) x = -α.contactHamiltonianVectorField f x := by
  rw [← neg_one_smul ℝ f, contactHamiltonianVectorField_const_smul, neg_one_smul]

/-! ### Vector fields whose Lie derivative is a multiple of `α` -/

/-- **Vector fields rescaling `α` preserve its kernel infinitesimally.** If the Lie derivative of
a one-form `α` along a vector field `V` is a multiple of `α` at `x`, and a vector field `Y`
differentiable at `x` is tangent to `ker α` near `x`, then the bracket `[V, Y]` is tangent to
`ker α` at `x`. No regularity of `V` is needed. -/
theorem mlieBracket_mem_kerDistribution_of_mlieDerivForm_eq_smul
    {V Y : (x : M) → TangentSpace I x} {x : M} {c : ℝ}
    (hL : mlieDerivForm V α.1 x = c • α.1 x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hYξ : ∀ᶠ y in 𝓝 x, Y y ∈ α.kerDistribution y) :
    VectorField.mlieBracket I V Y x ∈ α.kerDistribution x := by
  have hbr := mlieDerivForm_apply_vectorField (V := V) (X := ![Y]) (α.mdifferentiableAt x)
    (Fin.forall_fin_one.2 hY)
  -- `α(Y)` vanishes near `x`, so its derivative vanishes at `x`.
  have hzero : (fun y ↦ α.1 y fun _ ↦ Y y) =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
    filter_upwards [hYξ] with y hy
    rwa [mem_kerDistribution, Matrix.vec_single_eq_const] at hy
  simp only [Matrix.cons_val_fin_one, Fin.sum_univ_one, Function.update_eq_const_of_subsingleton,
    hL, ContinuousAlternatingMap.smul_apply, hzero.self_of_nhds, smul_zero, hzero.mvfderiv_eq,
    mvfderiv_const, zero_apply, zero_sub, zero_eq_neg] at hbr
  rw [mem_kerDistribution, Matrix.vec_single_eq_const]
  exact hbr

namespace IsContactForm

variable [FiniteDimensional ℝ E] (hα : α.IsContactForm)
include hα

/-- The contact flat map sends the contact Hamiltonian vector field of `f` to
`(R_α f + f) α - df`. -/
@[simp]
theorem contactFlat_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.contactFlat x (α.contactHamiltonianVectorField f x) =
      (mvfderiv I f x (α.reebVectorField x) + f x) • degreeOneEquiv α x - mvfderiv I f x :=
  (hα.isInvertible_contactFlat x).self_apply_inverse _

/-- **The first contact Hamiltonian equation**: `α(X_f) = f`. -/
@[simp]
theorem apply_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    α.1 x ![α.contactHamiltonianVectorField f x] = f x := by
  have h := congrArg (fun L ↦ L (α.reebVectorField x))
    (hα.contactFlat_contactHamiltonianVectorField f x)
  simp only [contactFlat_apply, hα.mextDeriv_reebVectorField_right, hα.apply_reebVectorField,
    zero_add, mul_one, sub_apply, smul_apply,
    degreeOneEquiv_apply_apply, smul_eq_mul] at h
  rw [← Matrix.vec_single_eq_const, hα.apply_reebVectorField] at h
  linarith

/-- **The second contact Hamiltonian equation**: `ι_(X_f) dα = (R_α f) α - df`. -/
@[simp]
theorem mextDeriv_contactHamiltonianVectorField_left (f : M → ℝ) (x : M)
    (w : TangentSpace I x) :
    mextDeriv α.1 x ![α.contactHamiltonianVectorField f x, w] =
      mvfderiv I f x (α.reebVectorField x) * α.1 x ![w] - mvfderiv I f x w := by
  have h := congrArg (fun L ↦ L w) (hα.contactFlat_contactHamiltonianVectorField f x)
  simp only [contactFlat_apply, hα.apply_contactHamiltonianVectorField,
    sub_apply, smul_apply, degreeOneEquiv_apply_apply,
    smul_eq_mul] at h
  rw [← Matrix.vec_single_eq_const] at h
  linarith

/-- **Characterization of the contact Hamiltonian vector field**: `X_f(x)` is the unique tangent
vector `v` with `α(v) = f(x)` and `ι_v dα = (R_α f) α - df` at `x`. -/
theorem eq_contactHamiltonianVectorField_iff {x : M} {v : TangentSpace I x} :
    v = α.contactHamiltonianVectorField f x ↔
      α.1 x ![v] = f x ∧ ∀ w : TangentSpace I x, mextDeriv α.1 x ![v, w] =
        mvfderiv I f x (α.reebVectorField x) * α.1 x ![w] - mvfderiv I f x w := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ (hα.isInvertible_contactFlat x).injective ?_⟩
  · rintro rfl
    exact ⟨hα.apply_contactHamiltonianVectorField f x,
      hα.mextDeriv_contactHamiltonianVectorField_left f x⟩
  rw [hα.contactFlat_contactHamiltonianVectorField]
  ext w
  simp only [contactFlat_apply, h₁, h₂, sub_apply,
    smul_apply, degreeOneEquiv_apply_apply, smul_eq_mul,
    ← Matrix.vec_single_eq_const]
  ring

/-- **Characterization of the contact Hamiltonian vector field**, tested on the contact
distribution: `X_f(x)` is the unique tangent vector `v` with `α(v) = f(x)` and
`dα(v, w) = -df(w)` for all `w ∈ ker α_x`. -/
theorem eq_contactHamiltonianVectorField_iff_kerDistribution {x : M} {v : TangentSpace I x} :
    v = α.contactHamiltonianVectorField f x ↔
      α.1 x ![v] = f x ∧ ∀ w : TangentSpace I x, α.1 x ![w] = 0 →
        mextDeriv α.1 x ![v, w] = -mvfderiv I f x w := by
  rw [hα.eq_contactHamiltonianVectorField_iff]
  refine and_congr_right fun _ ↦ ⟨fun h w hw ↦ by rw [h w, hw]; ring, fun h w ↦ ?_⟩
  -- Split `w` along `ξ ⊕ ℝ R_α` and use `dα(v, R_α) = 0`.
  set R := α.reebVectorField x
  set a := (degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ)
  set B := (mextDerivₗ I 1 α).bilinFormAt x
  have ha (u : TangentSpace I x) : α.1 x ![u] = a u := (degreeOneEquiv_coe_apply α x u).symm
  have hR : a R = 1 := by rw [← ha]; exact hα.apply_reebVectorField x
  have hw₀ : α.1 x ![w - a w • R] = 0 := by
    rw [ha, map_sub, map_smul, hR, smul_eq_mul, mul_one, sub_self]
  have hvR : B v R = 0 := by
    rw [← mextDeriv_apply_eq_bilinFormAt]; exact hα.mextDeriv_reebVectorField_right x _
  have := h _ hw₀
  rw [mextDeriv_apply_eq_bilinFormAt, map_sub, map_smul, smul_eq_mul, hvR, mul_zero, sub_zero,
    map_sub, map_smul, smul_eq_mul] at this
  rw [mextDeriv_apply_eq_bilinFormAt, this, ha]
  ring

/-- The contact Hamiltonian vector field of a constant function `c` is `c R_α`. -/
@[simp]
theorem contactHamiltonianVectorField_const (c : ℝ) (x : M) :
    α.contactHamiltonianVectorField (fun _ ↦ c) x = c • α.reebVectorField x := by
  simp [contactHamiltonianVectorField_def, mvfderiv_const,
    hα.reebVectorField_eq_contactFlatEquiv_symm]

/-- The contact Hamiltonian vector field of the constant function `1` is the Reeb vector field. -/
theorem contactHamiltonianVectorField_one (x : M) :
    α.contactHamiltonianVectorField (fun _ ↦ 1) x = α.reebVectorField x := by
  rw [hα.contactHamiltonianVectorField_const, one_smul]

/-- The contact Hamiltonian vector field of `f` is tangent to the contact distribution exactly
where `f` vanishes. -/
theorem contactHamiltonianVectorField_mem_kerDistribution_iff (x : M) :
    α.contactHamiltonianVectorField f x ∈ α.kerDistribution x ↔ f x = 0 := by
  rw [mem_kerDistribution, hα.apply_contactHamiltonianVectorField]

/-- The derivative of `f` along its contact Hamiltonian vector field is `df(X_f) = (R_α f) f`. -/
theorem mvfderiv_apply_contactHamiltonianVectorField (f : M → ℝ) (x : M) :
    mvfderiv I f x (α.contactHamiltonianVectorField f x) =
      mvfderiv I f x (α.reebVectorField x) * f x := by
  have h := hα.mextDeriv_contactHamiltonianVectorField_left f x
    (α.contactHamiltonianVectorField f x)
  rw [hα.apply_contactHamiltonianVectorField] at h
  have h₀ : mextDeriv α.1 x ![α.contactHamiltonianVectorField f x,
      α.contactHamiltonianVectorField f x] = 0 :=
    (mextDeriv α.1 x).map_eq_zero_of_eq ![_, _] (i := 0) (j := 1) rfl (by decide)
  linarith

/-! ### Regularity -/

/-- **Regularity of contact Hamiltonian vector fields.** For a contact form on a
finite-dimensional manifold, the contact Hamiltonian vector field of a `C^(n+1)` function is a
`C^n` vector field, for `n ≤ ∞`. -/
theorem contMDiff_contactHamiltonianVectorField {n : WithTop ℕ∞} (hn : n ≤ ∞)
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) :
    ContMDiff I I.tangent n (T% (α.contactHamiltonianVectorField f)) := by
  -- The function `x ↦ df_x (R_α x) + f x`.
  have hRf : ContMDiff I 𝓘(ℝ) n (fun x ↦ mvfderiv I f x (α.reebVectorField x) + f x) :=
    ((hf.contMDiff_mvfderiv_apply le_rfl).comp (hα.contMDiff_reebVectorField.of_le hn)).add
      (hf.of_le le_self_add)
  have hθ := (hRf.smul_section ((degreeOneEquiv α).contMDiff.of_le hn)).sub_section
    hf.contMDiff_totalSpaceMk_mvfderiv
  exact ((contMDiff_contactFlat α).clm_bundle_inverse hα.isInvertible_contactFlat).of_le
    hn |>.clm_bundle_apply hθ

/-! ### The Lie derivative of the contact form -/

/-- If a vector field `X` is differentiable at `x` and `X(x)` is the value at `x` of the contact
Hamiltonian vector field of `α(X)`, then `L_X α = R_α(α(X)) α` at `x`. -/
theorem mlieDerivForm_apply_of_eq_contactHamiltonianVectorField
    {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hXh : X x = α.contactHamiltonianVectorField (fun y ↦ α.1 y ![X y]) x) :
    mlieDerivForm X α.1 x =
      mvfderiv I (fun y ↦ α.1 y ![X y]) x (α.reebVectorField x) • α.1 x := by
  ext v
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, (FinVec.etaExpand_eq v).symm⟩
  rw [mlieDerivForm_apply_one (α.mdifferentiableAt x) hX, hXh,
    hα.mextDeriv_contactHamiltonianVectorField_left, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul]
  ring

/-- **The factor of a vector field rescaling `α`.** If `X` is differentiable at `x` and
`L_X α = c α` at `x`, then `c = R_α(α(X))` at `x`. -/
theorem eq_mvfderiv_reebVectorField_of_mlieDerivForm_eq_smul
    {X : (x : M) → TangentSpace I x} {x : M} {c : ℝ}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x)
    (hL : mlieDerivForm X α.1 x = c • α.1 x) :
    c = mvfderiv I (fun y ↦ α.1 y ![X y]) x (α.reebVectorField x) := by
  -- Evaluate both sides on the Reeb vector field.
  have h := congrArg (· ![α.reebVectorField x]) hL
  rwa [mlieDerivForm_apply_one (α.mdifferentiableAt x) hX, hα.mextDeriv_reebVectorField_right,
    zero_add, ContinuousAlternatingMap.smul_apply, hα.apply_reebVectorField, smul_eq_mul,
    mul_one, eq_comm] at h

/-- **The Lie derivative of `α` along a contact Hamiltonian vector field**: at a point where
`X_f` is differentiable, `L_(X_f) α = (R_α f) α`. This is the infinitesimal form of the fact that
the local flow of `X_f` preserves the contact distribution and its coorientation. -/
theorem mlieDerivForm_contactHamiltonianVectorField_apply {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) x) :
    mlieDerivForm (α.contactHamiltonianVectorField f) α.1 x =
      mvfderiv I f x (α.reebVectorField x) • α.1 x := by
  have hfun : (fun y ↦ α.1 y ![α.contactHamiltonianVectorField f y]) = f :=
    funext (hα.apply_contactHamiltonianVectorField f)
  simpa only [hfun] using
    hα.mlieDerivForm_apply_of_eq_contactHamiltonianVectorField hX (by rw [hfun])

/-- **Smooth contact Hamiltonian vector fields preserve the contact form up to a factor**: for a
`C²` function `f`, `L_(X_f) α = (R_α f) α`. -/
theorem mlieDerivForm_contactHamiltonianVectorField (hf : ContMDiff I 𝓘(ℝ) 2 f) :
    mlieDerivForm (α.contactHamiltonianVectorField f) α.1 =
      fun x ↦ mvfderiv I f x (α.reebVectorField x) • α.1 x :=
  funext fun x ↦ hα.mlieDerivForm_contactHamiltonianVectorField_apply <|
    ((hα.contMDiff_contactHamiltonianVectorField (n := 1) (by simp) hf) x).mdifferentiableAt
      one_ne_zero

/-- **Contact vector fields are contact Hamiltonian.** For a vector field `X` differentiable at
`x`, the Lie derivative `L_X α` is a multiple of `α` at `x` exactly when `X(x)` is the contact
Hamiltonian vector field of the function `α(X)` at `x`. The factor is then `R_α(α(X))` at `x`
(`TauCeti.SmoothForm.IsContactForm.eq_mvfderiv_reebVectorField_of_mlieDerivForm_eq_smul`). -/
theorem exists_mlieDerivForm_eq_smul_iff {X : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x) :
    (∃ c : ℝ, mlieDerivForm X α.1 x = c • α.1 x) ↔
      X x = α.contactHamiltonianVectorField (fun y ↦ α.1 y ![X y]) x := by
  refine ⟨fun ⟨c, hL⟩ ↦ hα.eq_contactHamiltonianVectorField_iff.2 ⟨rfl, fun w ↦ ?_⟩,
    fun hXh ↦ ⟨_, hα.mlieDerivForm_apply_of_eq_contactHamiltonianVectorField hX hXh⟩⟩
  have h := congrArg (· ![w]) hL
  rw [mlieDerivForm_apply_one (α.mdifferentiableAt x) hX, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, hα.eq_mvfderiv_reebVectorField_of_mlieDerivForm_eq_smul hX hL] at h
  linarith

/-- **Contact Hamiltonian vector fields preserve the contact distribution.** If `X_f` is
differentiable at `x`, and a vector field `Y` is differentiable at `x` and tangent to `ξ = ker α`
near `x`, then the bracket `[X_f, Y]` is tangent to `ξ` at `x`. The hypothesis on `X_f` holds for
instance when `f` is `C²`
(`TauCeti.SmoothForm.IsContactForm.contMDiff_contactHamiltonianVectorField`). -/
theorem mlieBracket_contactHamiltonianVectorField_mem_kerDistribution
    {Y : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I I.tangent
      (fun y ↦ (α.contactHamiltonianVectorField f y : TangentBundle I M)) x)
    (hY : MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x)
    (hYξ : ∀ᶠ y in 𝓝 x, Y y ∈ α.kerDistribution y) :
    VectorField.mlieBracket I (α.contactHamiltonianVectorField f) Y x ∈ α.kerDistribution x :=
  mlieBracket_mem_kerDistribution_of_mlieDerivForm_eq_smul
    (hα.mlieDerivForm_contactHamiltonianVectorField_apply hX) hY hYξ

end IsContactForm

end SmoothForm

end TauCeti
