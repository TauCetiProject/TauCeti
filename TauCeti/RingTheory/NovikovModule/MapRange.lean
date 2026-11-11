/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor
public import TauCeti.RingTheory.NovikovModule.TensorProduct
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Changing the coefficients of completed combinations

A ring homomorphism `ρ : R →+* R'` acts on completed combinations coefficientwise:
`NovikovModule.mapRange ρ a` has coefficient `ρ (a(s))` at every generator `s`. Since `ρ` sends
`0` to `0`, the nonzero coefficients of the result lie among those of `a`, so it is again finite
above every potential threshold. The result is a `ρ`-semilinear map
`NovikovModule R F →ₛₗ[ρ] NovikovModule R' F` which keeps every potential cutoff, hence is
continuous, and keeps every homogeneous piece.

Coefficient change is compatible with the operations given by supported kernels and with
completed tensor products. Applying `ρ` to the coefficients of a kernel `m` gives a kernel `ρ ∘ m`
with the same potential bound, and

* `mapRange ρ (kernelMap m a) = kernelMap (ρ ∘ m) (mapRange ρ a)`
  (`NovikovModule.mapRange_kernelMap`),
* `mapRange ρ (kernelProduct n a b) = kernelProduct (ρ ∘ n) (mapRange ρ a) (mapRange ρ b)`
  (`NovikovModule.mapRange_kernelProduct`),
* `ρ (kernelComp m m') = kernelComp (ρ ∘ m) (ρ ∘ m')` (`NovikovModule.map_kernelComp`),
* `mapRange ρ (tensor a b) = tensor (mapRange ρ a) (mapRange ρ b)`
  (`NovikovModule.mapRange_tensor`).

Every coefficient here is a sum with finitely many nonzero terms, which is what lets `ρ` pass
through it. Consequently every identity between kernels proved over `R`, such as `δ ∘ δ = 0`,
the Leibniz rule or a chain homotopy equation, holds for the transported kernels over `R'`, and
the coefficient change intertwines the corresponding chain-level operations.

On a finite union of torsors under a group `H` with equivariant potential, the lift coordinates
of `mapRange ρ a` are the coordinates of `a` with `ρ` applied to every coefficient
(`NovikovModule.coordinates_mapRange`). Hence coefficient change is semilinear over the
coefficient change `NovikovSeries.mapRingHom ρ` of Novikov rings
(`NovikovModule.novikovMapRange`) and sends each basis vector of chosen lifts to the
corresponding basis vector (`NovikovModule.mapRange_basis`), so it is the semilinear map
determined by these bases.

In Floer theory these are the coefficient changes between counts over `ℤ`, their reductions
over `ℤ/2` and their rational images. Signed counts of rigid moduli spaces give integral kernels,
their reductions modulo two are the unoriented counts, and their images in `ℚ` are what is
compared with rational virtual counts and with rational Gromov–Witten invariants.

## Main definitions

* `TauCeti.NovikovModule.mapRange`: the coefficientwise image of a completed combination under a
  ring homomorphism.
* `TauCeti.NovikovModule.novikovMapRange`: the same map on a finite union of torsors, as a
  semilinear map over the coefficient change of Novikov rings.

## Main results

* `TauCeti.NovikovModule.mapRange_injective`, `TauCeti.NovikovModule.mapRange_surjective`:
  coefficient change along an injective or surjective ring homomorphism is injective or
  surjective.
* `TauCeti.NovikovModule.continuous_mapRange`: coefficient change is continuous.
* `TauCeti.NovikovModule.mapRange_kernelMap`, `TauCeti.NovikovModule.mapRange_kernelProduct`,
  `TauCeti.NovikovModule.map_kernelComp`: compatibility with kernel maps, kernel products and
  composition of kernels.
* `TauCeti.NovikovModule.coordinates_mapRange`, `TauCeti.NovikovModule.mapRange_basis`:
  coefficient change in lift coordinates and on bases of lifts.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*,
  IAS/Park City Math. Ser. 7 (1999), 143–229, on Floer complexes over Novikov rings with
  coefficients in an arbitrary ring.
-/

public section

noncomputable section

open Function

namespace TauCeti

namespace NovikovModule

variable {R R' R'' S S₁ S₂ S₀ : Type*}

section Semiring

variable [Semiring R] [Semiring R'] [Semiring R''] {F : S → ℝ}

/-- Applying a function vanishing at `0` to the coefficients of a completed combination gives a
completed combination: its nonzero coefficients lie among those of the original one. -/
theorem comp_mem {f : R → R'} (hf : f 0 = 0) {a : S → R} (ha : a ∈ NovikovModule R F) :
    f ∘ a ∈ NovikovModule R' F :=
  mem_iff.2 fun C => (mem_iff.1 ha C).subset fun s hs => ⟨fun h => hs.1 (by simp [h, hf]), hs.2⟩

/-- The coefficient change of completed combinations along a ring homomorphism `ρ`: the
coefficient of `mapRange ρ a` at a generator `s` is `ρ (a(s))`. It is semilinear over `ρ`. -/
def mapRange (ρ : R →+* R') : NovikovModule R F →ₛₗ[ρ] NovikovModule R' F where
  toFun a := ⟨ρ ∘ a.val, comp_mem (map_zero ρ) a.property⟩
  map_add' a b := Subtype.ext <| funext fun s => map_add ρ (a.val s) (b.val s)
  map_smul' c a := Subtype.ext <| funext fun s => map_mul ρ c (a.val s)

/-- The coefficients of a coefficient change are the images of the coefficients. -/
@[simp]
theorem mapRange_apply_val (ρ : R →+* R') (a : NovikovModule R F) (s : S) :
    (mapRange ρ a).val s = ρ (a.val s) :=
  (rfl)

/-- Changing coefficients along the identity does nothing. -/
@[simp]
theorem mapRange_id (a : NovikovModule R F) : mapRange (RingHom.id R) a = a :=
  (rfl)

/-- Two successive coefficient changes are the coefficient change along the composite. -/
@[simp]
theorem mapRange_mapRange (ρ : R →+* R') (ρ' : R' →+* R'') (a : NovikovModule R F) :
    mapRange ρ' (mapRange ρ a) = mapRange (ρ'.comp ρ) a :=
  (rfl)

/-- Coefficient change along an injective ring homomorphism is injective. -/
theorem mapRange_injective {ρ : R →+* R'} (hρ : Injective ρ) :
    Injective (mapRange (F := F) ρ) :=
  fun a b h => Subtype.ext <| funext fun s => hρ (by simpa using congrArg (·.val s) h)

/-- Coefficient change along a surjective ring homomorphism is surjective: a completed combination
over `R'` lifts coefficientwise, keeping the zero coefficients zero. -/
theorem mapRange_surjective {ρ : R →+* R'} (hρ : Surjective ρ) :
    Surjective (mapRange (F := F) ρ) := by
  classical
  intro b
  refine ⟨⟨fun s => if b.val s = 0 then 0 else surjInv hρ (b.val s),
    mem_iff.2 fun C => (finite_gt b C).subset fun s hs => ⟨fun h => hs.1 (by simp [h]), hs.2⟩⟩,
    ?_⟩
  ext s
  by_cases h : b.val s = 0 <;> simp [h, surjInv_eq hρ]

/-- Coefficient change of a finite combination is the coefficient change of finitely supported
functions. -/
@[simp]
theorem mapRange_ofFinsupp (ρ : R →+* R') (a : S →₀ R) :
    mapRange ρ (ofFinsupp F a) = ofFinsupp F (Finsupp.mapRange ρ (map_zero ρ) a) := by
  ext s
  simp

/-- Coefficient change of a point mass is the point mass of the image coefficient. -/
@[simp]
theorem mapRange_single [DecidableEq S] (ρ : R →+* R') (s : S) (r : R) :
    mapRange ρ (single s r : NovikovModule R F) = single s (ρ r) := by
  ext t
  by_cases h : t = s
  · subst h
    simp
  · simp [h]

/-- Truncation above a potential threshold commutes with coefficient change. -/
@[simp]
theorem trunc_mapRange (ρ : R →+* R') (C : ℝ) (a : NovikovModule R F) :
    trunc C (mapRange ρ a) = Finsupp.mapRange ρ (map_zero ρ) (trunc C a) := by
  ext s
  simp only [trunc_apply, mapRange_apply_val, Finsupp.mapRange_apply]
  split_ifs <;> simp

/-- Coefficient change keeps homogeneous combinations homogeneous of the same degree. -/
theorem mapRange_mem_gradeBy {D : Type*} (ρ : R →+* R') {d : S → D} {k : D}
    {a : NovikovModule R F} (ha : a ∈ gradeBy R F d k) :
    mapRange ρ a ∈ gradeBy R' F d k :=
  mem_gradeBy_iff.2 fun s hs => mem_gradeBy_iff.1 ha s fun h => hs (by simp [h])

section KernelMap

variable {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {C C' : ℝ} (ρ : R →+* R')

/-- **Coefficient change of a kernel map.** Changing the coefficients of the image of `a` under
the map of a kernel `m` is the same as applying the map of the kernel `ρ ∘ m` to the coefficient
change of `a`. The transported kernel may be given any potential bound. -/
theorem mapRange_kernelMap {m : S₁ → S₀ → R}
    (hm : ∀ p₁ p₀, m p₁ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C) (hmfin : ∀ p₁, m p₁ ∈ NovikovModule R F₀)
    (hm' : ∀ p₁ p₀, ρ (m p₁ p₀) ≠ 0 → F₀ p₀ ≤ F₁ p₁ + C')
    (hmfin' : ∀ p₁, (fun p₀ => ρ (m p₁ p₀)) ∈ NovikovModule R' F₀) (a : NovikovModule R F₁) :
    mapRange ρ (kernelMap hm hmfin a) = kernelMap hm' hmfin' (mapRange ρ a) := by
  ext p₀
  simp only [mapRange_apply_val, kernelMap_apply_val]
  rw [map_finsum ρ (finite_support_mul_kernelMap hm a p₀)]
  simp only [map_mul]

/-- **Coefficient change of a composite kernel.** If `m` has completed output at `p₁` and `m'`
is supported, then the image of the composite kernel is the composite of the image kernels. -/
theorem map_kernelComp {m : S₁ → S₀ → R} {m' : S₀ → S₂ → R} {p₁ : S₁} {p₂ : S₂}
    (hmfin : m p₁ ∈ NovikovModule R F₀) (hm' : ∀ p₀, m' p₀ p₂ ≠ 0 → F₂ p₂ ≤ F₀ p₀ + C') :
    ρ (kernelComp m m' p₁ p₂) =
      kernelComp (fun p₁ p₀ => ρ (m p₁ p₀)) (fun p₀ p₂ => ρ (m' p₀ p₂)) p₁ p₂ := by
  rw [kernelComp_apply, kernelComp_apply, map_finsum ρ (finite_support_mul (T := F₂ p₂ - C')
    (fun p₀ h => by linarith [hm' p₀ h]) ⟨m p₁, hmfin⟩)]
  simp only [map_mul]

end KernelMap

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring R'] {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ}
  {C C' : ℝ} (ρ : R →+* R')

/-- **Coefficient change of a kernel product.** Changing the coefficients of the product of `a`
and `b` given by a kernel `n` is the same as multiplying their coefficient changes with the
kernel `ρ ∘ n`. The transported kernel may be given any potential bound. -/
theorem mapRange_kernelProduct {n : S₁ → S₂ → S₀ → R}
    (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
    (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
    (hn' : ∀ p₁ p₂ p₀, ρ (n p₁ p₂ p₀) ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C')
    (hfin' : ∀ p₁ p₂, (fun p₀ => ρ (n p₁ p₂ p₀)) ∈ NovikovModule R' F₀)
    (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    mapRange ρ (kernelProduct hn hfin a b) =
      kernelProduct hn' hfin' (mapRange ρ a) (mapRange ρ b) := by
  ext p₀
  simp only [mapRange_apply_val, kernelProduct_apply_val]
  rw [map_finsum ρ (finite_support_mul_kernel hn a b p₀)]
  simp only [map_mul]

/-- Coefficient change of a completed tensor product is the tensor product of the coefficient
changes. -/
@[simp]
theorem mapRange_tensor (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    mapRange ρ (tensor a b) = tensor (mapRange ρ a) (mapRange ρ b) := by
  ext q
  simp

/-- Coefficient change of a completed external product is the external product of the
coefficient changes. -/
@[simp]
theorem mapRange_externalProduct (a : NovikovModule R F₁) (b : NovikovModule R F₂) :
    mapRange ρ (externalProduct a b) = externalProduct (mapRange ρ a) (mapRange ρ b) := by
  ext q
  simp

end CommSemiring

section Ring

variable [Ring R] [Ring R'] {F : S → ℝ} (ρ : R →+* R')

/-- Coefficient change keeps every potential cutoff: a combination vanishing above `C` is sent to
a combination vanishing above `C`. -/
theorem mapRange_mem_potentialFiltration {C : ℝ} {a : NovikovModule R F}
    (ha : a ∈ potentialFiltration R F C) : mapRange ρ a ∈ potentialFiltration R' F C :=
  mem_potentialFiltration.2 fun s hs => by simp [mem_potentialFiltration.1 ha s hs]

/-- Coefficient change is continuous for the potential-cutoff topologies. -/
theorem continuous_mapRange : Continuous (mapRange (F := F) ρ) :=
  continuous_of_forall_mem_potentialFiltration (mapRange ρ) fun C =>
    ⟨C, fun _ ha => mapRange_mem_potentialFiltration ρ ha⟩

end Ring

section Coordinates

variable [Semiring R] [Semiring R'] {H ι : Type*} [AddGroup H] [Finite ι] {P : ι → Type*}
  [∀ i, AddTorsor H (P i)] {N : H →+ ℝ} {F : (Σ i, P i) → ℝ}
  (hF : ∀ i h (p : P i), F ⟨i, h +ᵥ p⟩ = F ⟨i, p⟩ - N h) (ρ : R →+* R')

/-- In any lift coordinates, coefficient change of completed combinations is coefficient change
of Novikov series. -/
@[simp]
theorem coordinates_mapRange (r : ∀ i, P i) (a : NovikovModule R F) (i : ι) :
    coordinates hF r (mapRange ρ a) i =
      NovikovSeries.mapRingHom ρ (AddMonoidHom.id H) NovikovSeries.exists_period_rescale_id
        (coordinates hF r a i) := by
  ext h
  simp

/-- Coefficient change is semilinear for the Novikov module structures of
`TauCeti.NovikovModule.module`, over the coefficient change of Novikov rings. -/
theorem mapRange_smul (β : NovikovSeries R H N) (a : NovikovModule R F) :
    letI := module (R := R) hF
    letI := module (R := R') hF
    mapRange ρ (β • a) =
      NovikovSeries.mapRingHom ρ (AddMonoidHom.id H) NovikovSeries.exists_period_rescale_id β •
        mapRange ρ a := by
  let := module (R := R) hF
  let := module (R := R') hF
  let r := fun i => Classical.arbitrary (P i)
  refine (coordinates hF r).injective (funext fun i => ?_)
  simp only [coordinates_smul, Pi.smul_apply, smul_eq_mul, map_mul, coordinates_mapRange]

/-- Coefficient change on a finite union of torsors, as a semilinear map over the coefficient
change `NovikovSeries.mapRingHom ρ` of Novikov rings, for the Novikov module structures of
`TauCeti.NovikovModule.module`. -/
def novikovMapRange :
    letI := module (R := R) hF
    letI := module (R := R') hF
    NovikovModule R F →ₛₗ[NovikovSeries.mapRingHom (N := N) (N' := N) ρ (AddMonoidHom.id H)
      NovikovSeries.exists_period_rescale_id] NovikovModule R' F :=
  letI := module (R := R) hF
  letI := module (R := R') hF
  { toFun := mapRange ρ
    map_add' := map_add _
    map_smul' := mapRange_smul hF ρ }

/-- The Novikov-semilinear coefficient change evaluates to the coefficient change. -/
@[simp]
theorem novikovMapRange_apply (a : NovikovModule R F) :
    novikovMapRange hF ρ a = mapRange ρ a :=
  (rfl)

/-- Coefficient change sends each basis vector of chosen lifts to the basis vector of the same
lifts. Together with `TauCeti.NovikovModule.novikovMapRange`, this says that coefficient change
is the `NovikovSeries.mapRingHom ρ`-semilinear map determined by these bases. -/
@[simp]
theorem mapRange_basis (r : ∀ i, P i) (i : ι) :
    mapRange ρ (basis (R := R) hF r i) = basis (R := R') hF r i := by
  classical
  refine (coordinates hF r).injective (funext fun j => ?_)
  rw [coordinates_mapRange, coordinates_basis, coordinates_basis]
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

end Coordinates

end NovikovModule

end TauCeti
