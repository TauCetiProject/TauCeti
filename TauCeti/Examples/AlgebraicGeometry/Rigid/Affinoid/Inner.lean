/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Inner
public import TauCeti.RingTheory.Affinoid.Subdomain.Laurent

/-!
# Inner subdomains of the closed unit disc

A closed disc `{|T| ≤ |c|⁻¹}` of radius less than one, presented as the Laurent domain
`{|c T| ≤ 1}`, is relatively compact in the closed unit disc over `K`: the identity presentation
of `K⟨T⟩` already has its variable bounded by `|c|⁻¹ < 1` there. The unit disc itself is not
inner in itself over `K`, whereas the one-point space `Sp K` is, being finite over `K`.
-/

public section

namespace TauCeti.Examples

open _root_.MvPowerSeries TauCeti.MvPowerSeries TauCeti.AffinoidSubdomain

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

-- A smaller closed disc is inner in the unit disc over `K`.
example {c : K} (hc : 1 < ‖c‖) :
    (ofMap (LaurentFraction.isAffinoidSubdomainMap isAffinoidAlgebra_tate
      (f := ![c • ⟨X 0, isRestricted_X _ 0⟩])
      (g := (Fin.elim0 : Fin 0 → IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1))))).IsInner
      (Algebra.ofId K (IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1))) := by
  refine (isInner_iff_forall_pointNorm_lt isAffinoidAlgebra_tate).mpr
    ⟨1, AlgHom.id K _, Function.surjective_id, fun a ↦ by simp, fun i y hy ↦ ?_⟩
  obtain rfl := Subsingleton.elim i 0
  have hy := (mem_ofMap _ y).mp hy |> mem_laurentDomain.mp |>.1 0
  rw [Matrix.cons_val_zero, y.pointNorm_smul] at hy
  have hc0 : 0 < ‖c‖ := one_pos.trans hc
  rw [AlgHom.id_apply]
  by_contra! h
  linarith [mul_le_mul_of_nonneg_left h hc0.le]

-- The closed unit disc is not inner in itself over `K`.
example : ¬ (univ (isAffinoidAlgebra_tate (K := K) (σ := Fin 1))).IsInner
    (Algebra.ofId K (IsRestricted.subring (R := K) (fun _ : Fin 1 ↦ 1))) :=
  not_isInner_univ_tate

-- A point, finite over `K`, is inner in itself over `K`.
example : (univ (isAffinoidAlgebra_self (K := K))).IsInner (AlgHom.id K K) :=
  isInner_univ_of_finite isAffinoidAlgebra_self isAffinoidAlgebra_self (AlgHom.Finite.id K K)

end TauCeti.Examples
