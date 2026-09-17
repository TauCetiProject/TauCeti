import TauCeti.RepresentationTheory.CharacterTable.Solvable
import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
import TauCeti.RepresentationTheory.Symmetric.TensorAction.GeneralLinear
import SubVerso.Examples
open SubVerso.Examples

%example burnside
open TauCeti in
/-- Burnside's theorem — every finite group of order pᵃqᵇ, for primes p and q,
is solvable. -/
theorem burnside {G : Type*} [Group G] [Finite G] {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (h : Nat.card G = p ^ a * q ^ b) :
    Group.IsSolvable G :=
  isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq h
%end

%example caratheodory
open TauCeti Set Metric Bornology in
/-- Carathéodory's boundary extension theorem — a Riemann map onto a Jordan
domain extends to a homeomorphism of the closures. -/
theorem caratheodory {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧ BijOn g (ball 0 1) Ω ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ closure Ω,
        ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = g z :=
  exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier hΩo hΩc hΩb hΩJ
%end

%example schur_weyl
open TauCeti in
/-- Schur–Weyl duality — on the d-th tensor power of kⁿ, the images of the
general linear and symmetric group algebras are each other's centralizers. -/
theorem schur_weyl {k : Type*} [Field k] [Infinite k] {n d : ℕ}
    [NeZero (Nat.factorial d : k)] :
    Subalgebra.centralizer k (Set.range ⇑(tensorPowerRep k n d).asAlgebraHom) =
        (permTensorActionAlgHom k n d).range ∧
      Subalgebra.centralizer k (Set.range ⇑(permTensorActionAlgHom k n d)) =
        (tensorPowerRep k n d).asAlgebraHom.range :=
  ⟨centralizer_range_tensorPowerRep_asAlgebraHom_eq_range_permTensorActionAlgHom,
    centralizer_range_permTensorActionAlgHom_eq_range_tensorPowerRep_asAlgebraHom⟩
%end
