/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.NovikovModule.Tensor
public import TauCeti.Algebra.Homology.SquareZero.Graded

/-!
# Comparing a kernel product with a product transported along chain maps

Let `⋆` be the product of completed combinations given by a supported product kernel
`n(p₁, p₂, p₀)` on generators `Sₗ` (`TauCeti.NovikovModule.kernelProduct`), and let `⋆_q` be the
product given by a second product kernel `q(t₁, t₂, t₀)` on generators `Tₗ`. Let `φ₁`, `φ₂`, `φ₀`
be kernels from each `Tₗ` to `Sₗ`, and let `ψ₀` be a kernel from `S₀` back to `T₀`. Applying `φ₁`
and `φ₂`, multiplying with `⋆` and returning with `ψ₀` is a kernel map out of the completed tensor
product `a ⊗ b`, with the kernel `∑ₚ (φ₁ ⊗ φ₂)(t, p) ∑ₛ n(p₁, p₂, s) ψ₀(s, t₀)`.

In Floer theory the `Sₗ` are capped orbits and `⋆` is the pair-of-pants product, the `Tₗ` are
critical points of Morse functions with Novikov coefficients and `⋆_q` is the Morse quantum
product, `φₗ` count Piunikhin–Salamon–Schwarz (PSS) half-cylinders from Morse to Floer complexes,
and `ψ₀` counts PSS half-cylinders in the opposite direction. Attaching PSS planes to the three
ends of a pair of pants and deforming the Hamiltonian perturbation to zero gives a one-parameter
family of three-pointed spheres. One end of the family is the broken configuration counted by
`ψ₀ (φ₁ a ⋆ φ₂ b)`; the other is the unperturbed three-pointed genus-zero problem counted by
`a ⋆_q b`. The remaining codimension-one boundary points of its one-dimensional moduli spaces are
breakings at the three Morse ends, so counting all boundary points gives the kernel identity

`∑ₚ (φ₁ ⊗ φ₂)(t, p) ∑ₛ n(p₁, p₂, s) ψ₀(s, t₀) - q(t₁, t₂, t₀) = (k η₀ + D k)(t, t₀)`

for the kernel `k` counting rigid elements of the family, the output differential `η₀` and the
differential `D` of the tensor product of the inputs. It gives the chain homotopy

`ψ₀ (φ₁ a ⋆ φ₂ b) - a ⋆_q b = η₀ (K x) + K (D x)`,  `x = a ⊗ b`

(`NovikovModule.kernelMap_kernelProduct_kernelMap_sub_kernelProduct`). This compares the products
through the inverse `ψ₀`, whereas a comparison of products should move the Morse product forward
with `φ₀`. If `h₀` is a kernel homotopy `φ₀ ψ₀ - 1 = δ₀ h₀ + h₀ δ₀` for the output differential
`δ₀`, which a module inverse of the PSS map supplies, then writing `T = φ₁ a ⋆ φ₂ b`,

`T - φ₀ (a ⋆_q b) = δ₀ (φ₀ (K x) - h₀ T) + (φ₀ (K (D x)) - h₀ (δ₀ T))`

for homogeneous `a` and `b`, when `φ₀` is a chain map of degree zero and `K` has degree `ε - 1`
(`NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct`). When `T` is itself a chain
map, `δ₀ T = T D`, this is the chain homotopy `T - φ₀ Q = δ₀ (φ₀ K - h₀ T) + (φ₀ K - h₀ T) D`
between the two maps out of the tensor product. On cocycles both `D x` and `δ₀ T` vanish, so the
difference is a coboundary
(`NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct_mem_coboundaries`), and the
maps induced on degree-wise cohomology by `φ₁`, `φ₂`, `φ₀` intertwine `⋆_q` with `⋆`
(`NovikovModule.cohomologyMap_cohomologyProduct_kernelProduct_of_homotopy_inverse`). This is the
algebraic form of the multiplicativity of the PSS map. Only the output needs the inverse kernel
`ψ₀` and the homotopy `h₀`; the input maps `φ₁` and `φ₂` need no inverses. Neither product is
defined by transporting the other: `⋆` and `⋆_q` are both given by their own kernels. The kernel
identities and potential bounds remain hypotheses: they are the geometric input from the
compactified moduli spaces, and the module inverse of the PSS map.

## Main results

* `NovikovModule.kernelMap_kernelProduct_kernelMap_sub_kernelProduct`: a kernel homotopy between
  the transported kernel and `q` gives a chain homotopy between `ψ₀ (φ₁ a ⋆ φ₂ b)` and `a ⋆_q b`.
* `NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct`: combined with a homotopy
  `φ₀ ψ₀ - 1 = δ₀ h₀ + h₀ δ₀`, it gives a homotopy between `φ₁ a ⋆ φ₂ b` and `φ₀ (a ⋆_q b)`.
* `NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct_mem_coboundaries`: on cocycles
  the two differ by a coboundary.
* `NovikovModule.cohomologyMap_cohomologyProduct_kernelProduct_of_homotopy_inverse`: the maps
  induced on cohomology by `φ₁`, `φ₂`, `φ₀` intertwine the two products.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, the chapter on Floer
  homology and the Piunikhin–Salamon–Schwarz isomorphism.
-/

public section

noncomputable section

namespace TauCeti

namespace NovikovModule

variable {R S₁ S₂ S₀ T₁ T₂ T₀ : Type*} [CommRing R]
  {F₁ : S₁ → ℝ} {F₂ : S₂ → ℝ} {F₀ : S₀ → ℝ} {G₁ : T₁ → ℝ} {G₂ : T₂ → ℝ} {G₀ : T₀ → ℝ}
  {C Cq C₁ C₂ C₀ Cψ Ck Ch Cδ Cη : ℝ}
  {n : S₁ → S₂ → S₀ → R} {q : T₁ → T₂ → T₀ → R}
  {φ₁ : T₁ → S₁ → R} {φ₂ : T₂ → S₂ → R} {φ₀ : T₀ → S₀ → R} {ψ₀ : S₀ → T₀ → R}
  {k : T₁ × T₂ → T₀ → R} {h₀ : S₀ → S₀ → R} {δ₀ : S₀ → S₀ → R} {η₀ : T₀ → T₀ → R}
  (hn : ∀ p₁ p₂ p₀, n p₁ p₂ p₀ ≠ 0 → F₀ p₀ ≤ F₁ p₁ + F₂ p₂ + C)
  (hfin : ∀ p₁ p₂, n p₁ p₂ ∈ NovikovModule R F₀)
  (hq : ∀ t₁ t₂ t₀, q t₁ t₂ t₀ ≠ 0 → G₀ t₀ ≤ G₁ t₁ + G₂ t₂ + Cq)
  (hqfin : ∀ t₁ t₂, q t₁ t₂ ∈ NovikovModule R G₀)
  (hφ₁ : ∀ t p, φ₁ t p ≠ 0 → F₁ p ≤ G₁ t + C₁) (hφ₁fin : ∀ t, φ₁ t ∈ NovikovModule R F₁)
  (hφ₂ : ∀ t p, φ₂ t p ≠ 0 → F₂ p ≤ G₂ t + C₂) (hφ₂fin : ∀ t, φ₂ t ∈ NovikovModule R F₂)
  (hφ₀ : ∀ t p, φ₀ t p ≠ 0 → F₀ p ≤ G₀ t + C₀) (hφ₀fin : ∀ t, φ₀ t ∈ NovikovModule R F₀)
  (hψ₀ : ∀ p t, ψ₀ p t ≠ 0 → G₀ t ≤ F₀ p + Cψ) (hψ₀fin : ∀ p, ψ₀ p ∈ NovikovModule R G₀)
  (hk : ∀ (t : T₁ × T₂) t₀, k t t₀ ≠ 0 → G₀ t₀ ≤ G₁ t.1 + G₂ t.2 + Ck)
  (hkfin : ∀ t, k t ∈ NovikovModule R G₀)
  (hh₀ : ∀ p p', h₀ p p' ≠ 0 → F₀ p' ≤ F₀ p + Ch) (hh₀fin : ∀ p, h₀ p ∈ NovikovModule R F₀)
  (hδ₀ : ∀ p p', δ₀ p p' ≠ 0 → F₀ p' ≤ F₀ p + Cδ) (hδ₀fin : ∀ p, δ₀ p ∈ NovikovModule R F₀)
  (hη₀ : ∀ t t', η₀ t t' ≠ 0 → G₀ t' ≤ G₀ t + Cη) (hη₀fin : ∀ t, η₀ t ∈ NovikovModule R G₀)

section Homotopy

/-- **Comparison through the inverse, up to homotopy.** Let `n` and `q` be product kernels, let
`φ₁`, `φ₂` be kernels from the input generators of `q` to those of `n`, let `ψ₀` be a kernel from
the output generators of `n` to those of `q`, let `η₀` be a kernel on the output generators of
`q`, and let `D` be a kernel on pairs of input generators of `q`. If a kernel `k` is a kernel
homotopy,

`∑ₚ (φ₁ ⊗ φ₂)(t, p) ∑ₛ n(p₁, p₂, s) ψ₀(s, t₀) - q(t₁, t₂, t₀) = (k η₀ + D k)(t, t₀)`,

then its kernel map `K` is a homotopy between the two maps out of the tensor product: for
`x = a ⊗ b`, `ψ₀ (φ₁ a ⋆ φ₂ b) - a ⋆_q b = η₀ (K x) + K (D x)`. -/
theorem kernelMap_kernelProduct_kernelMap_sub_kernelProduct
    {D : T₁ × T₂ → T₁ × T₂ → R} {CD : ℝ}
    (hD : ∀ t t', D t t' ≠ 0 → G₁ t'.1 + G₂ t'.2 ≤ G₁ t.1 + G₂ t.2 + CD)
    (hDfin : ∀ t, D t ∈ NovikovModule R fun t' : T₁ × T₂ => G₁ t'.1 + G₂ t'.2)
    (hcomp : ∀ (t : T₁ × T₂) t₀,
      kernelComp (kernelComp (kernelTensor φ₁ φ₂) fun p : S₁ × S₂ => n p.1 p.2) ψ₀ t t₀ -
          q t.1 t.2 t₀ =
        kernelComp k η₀ t t₀ + kernelComp D k t t₀)
    (a : NovikovModule R G₁) (b : NovikovModule R G₂) :
    kernelMap hψ₀ hψ₀fin
          (kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b)) -
        kernelProduct hq hqfin a b =
      kernelMap hη₀ hη₀fin (kernelMap hk hkfin (tensor a b)) +
        kernelMap hk hkfin (kernelMap hD hDfin (tensor a b)) := by
  -- Both sides of the comparison are kernel maps out of the tensor product, of the transported
  -- kernel and of `q`.
  have hn₂ (p : S₁ × S₂) (p₀ : S₀) (h : n p.1 p.2 p₀ ≠ 0) : F₀ p₀ ≤ F₁ p.1 + F₂ p.2 + C :=
    hn p.1 p.2 p₀ h
  have hq₂ (t : T₁ × T₂) (t₀ : T₀) (h : q t.1 t.2 t₀ ≠ 0) : G₀ t₀ ≤ G₁ t.1 + G₂ t.2 + Cq :=
    hq t.1 t.2 t₀ h
  have hT (t : T₁ × T₂) (p : S₁ × S₂) (h : kernelTensor φ₁ φ₂ t p ≠ 0) :
      F₁ p.1 + F₂ p.2 ≤ G₁ t.1 + G₂ t.2 + (C₁ + C₂) :=
    potential_le_of_kernelTensor_ne_zero hφ₁ hφ₂ h
  have hTfin := kernelTensor_mem hφ₁fin hφ₂fin
  have hτ (t : T₁ × T₂) (p₀ : S₀)
      (h : kernelComp (kernelTensor φ₁ φ₂) (fun p : S₁ × S₂ => n p.1 p.2) t p₀ ≠ 0) :
      F₀ p₀ ≤ G₁ t.1 + G₂ t.2 + (C₁ + C₂ + C) := by
    linarith [potential_le_of_kernelComp_ne_zero (hT t) (hn₂ · p₀) h]
  have hτfin (t : T₁ × T₂) := kernelComp_mem hn₂ (fun p => hfin p.1 p.2) (hTfin t)
  have hτψ (t : T₁ × T₂) (t₀ : T₀)
      (h : kernelComp (kernelComp (kernelTensor φ₁ φ₂) fun p : S₁ × S₂ => n p.1 p.2) ψ₀ t t₀ ≠
        0) :
      G₀ t₀ ≤ G₁ t.1 + G₂ t.2 + (C₁ + C₂ + C + Cψ) := by
    linarith [potential_le_of_kernelComp_ne_zero (hτ t) (hψ₀ · t₀) h]
  rw [kernelProduct_eq_kernelMap_tensor hn hfin hn₂ (fun p => hfin p.1 p.2),
    ← kernelMap_kernelTensor_tensor hφ₁ hφ₁fin hφ₂ hφ₂fin hT hTfin,
    kernelMap_kernelMap hT hTfin hn₂ (fun p => hfin p.1 p.2) hτ hτfin,
    kernelMap_kernelMap hτ hτfin hψ₀ hψ₀fin hτψ fun t => kernelComp_mem hψ₀ hψ₀fin (hτfin t),
    kernelProduct_eq_kernelMap_tensor hq hqfin hq₂ fun t => hqfin t.1 t.2]
  exact kernelMap_sub_kernelMap _ _ _ _ hk hkfin hD hDfin hη₀ hη₀fin hcomp _

include hψ₀ hψ₀fin in
/-- **Comparison along the chain maps, up to homotopy.** Under the kernel homotopy of
`NovikovModule.kernelMap_kernelProduct_kernelMap_sub_kernelProduct`, suppose that `h₀` is a kernel
homotopy between `φ₀ ψ₀` and the identity on the output generators of `n`,

`∑ₜ ψ₀(p, t) φ₀(t, p') - [p = p'] = (h₀ δ₀ + δ₀ h₀)(p, p')`,

that `k` has degree `ε - 1` for degree functions `e₁`, `e₂`, `e₀`, and that `φ₀` commutes with the
differentials `η₀` and `δ₀` on homogeneous combinations. Then for homogeneous `a` and `b`, with
`x = a ⊗ b` and `T = φ₁ a ⋆ φ₂ b`,

`T - φ₀ (a ⋆_q b) = δ₀ (φ₀ (K x) - h₀ T) + (φ₀ (K (D x)) - h₀ (δ₀ T))`.

When `T` commutes with the differentials, `δ₀ T = T D`, the right-hand side is
`δ₀ (φ₀ K - h₀ T) x + (φ₀ K - h₀ T) (D x)`. -/
theorem kernelProduct_kernelMap_sub_kernelMap_kernelProduct [DecidableEq S₀]
    {e₁ : T₁ → ℤ} {e₂ : T₂ → ℤ} {e₀ : T₀ → ℤ} {ε : ℤ}
    {D : T₁ × T₂ → T₁ × T₂ → R} {CD : ℝ}
    (hD : ∀ t t', D t t' ≠ 0 → G₁ t'.1 + G₂ t'.2 ≤ G₁ t.1 + G₂ t.2 + CD)
    (hDfin : ∀ t, D t ∈ NovikovModule R fun t' : T₁ × T₂ => G₁ t'.1 + G₂ t'.2)
    (hkd : ∀ (t : T₁ × T₂) t₀, k t t₀ ≠ 0 → e₀ t₀ = e₁ t.1 + e₂ t.2 + (ε - 1))
    (hφ₀D : ∀ {i : ℤ} {a : NovikovModule R G₀}, a ∈ gradeBy R G₀ e₀ i →
      kernelMap hδ₀ hδ₀fin (kernelMap hφ₀ hφ₀fin a) =
        kernelMap hφ₀ hφ₀fin (kernelMap hη₀ hη₀fin a))
    (hcomp : ∀ (t : T₁ × T₂) t₀,
      kernelComp (kernelComp (kernelTensor φ₁ φ₂) fun p : S₁ × S₂ => n p.1 p.2) ψ₀ t t₀ -
          q t.1 t.2 t₀ =
        kernelComp k η₀ t t₀ + kernelComp D k t t₀)
    (hinv : ∀ p p', kernelComp ψ₀ φ₀ p p' - (if p = p' then 1 else 0) =
      kernelComp h₀ δ₀ p p' + kernelComp δ₀ h₀ p p')
    {i j : ℤ} {a : NovikovModule R G₁} (ha : a ∈ gradeBy R G₁ e₁ i)
    {b : NovikovModule R G₂} (hb : b ∈ gradeBy R G₂ e₂ j) :
    kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) -
        kernelMap hφ₀ hφ₀fin (kernelProduct hq hqfin a b) =
      kernelMap hδ₀ hδ₀fin (kernelMap hφ₀ hφ₀fin (kernelMap hk hkfin (tensor a b)) -
          kernelMap hh₀ hh₀fin
            (kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b))) +
        (kernelMap hφ₀ hφ₀fin (kernelMap hk hkfin (kernelMap hD hDfin (tensor a b))) -
          kernelMap hh₀ hh₀fin (kernelMap hδ₀ hδ₀fin
            (kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b)))) := by
  -- The comparison through the inverse `ψ₀`.
  have hψ := kernelMap_kernelProduct_kernelMap_sub_kernelProduct hn hfin hq hqfin hφ₁ hφ₁fin hφ₂
    hφ₂fin hψ₀ hψ₀fin hk hkfin hη₀ hη₀fin hD hDfin hcomp a b
  -- The homotopy inverse: `φ₀ (ψ₀ y) - y = δ₀ (h₀ y) + h₀ (δ₀ y)`.
  have hψφ (p p' : S₀) (h : kernelComp ψ₀ φ₀ p p' ≠ 0) : F₀ p' ≤ F₀ p + (Cψ + C₀) := by
    linarith [potential_le_of_kernelComp_ne_zero (hψ₀ p) (hφ₀ · p') h]
  have hψφfin (p : S₀) := kernelComp_mem hφ₀ hφ₀fin (hψ₀fin p)
  have hid := kernelMap_sub_kernelMap hψφ hψφfin
    (fun p p' h => potential_le_of_diagonal_ne_zero (s := fun _ => (1 : R)) h)
    (diagonal_mem fun _ => 1) hh₀ hh₀fin hδ₀ hδ₀fin hδ₀ hδ₀fin hinv
    (kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b))
  rw [← kernelMap_kernelMap hψ₀ hψ₀fin hφ₀ hφ₀fin hψφ hψφfin, kernelMap_eq_id,
    LinearMap.id_apply] at hid
  -- `φ₀` is a chain map on the homogeneous combination `K x`, of degree `i + j + (ε - 1)`.
  have hφη := hφ₀D (kernelMap_mem_gradeBy hk hkfin (d₁ := fun t : T₁ × T₂ => e₁ t.1 + e₂ t.2) hkd
    (tensor_mem_gradeBy ha hb))
  -- Substitute `a ⋆_q b = ψ₀ T - η₀ (K x) - K (D x)`, move `φ₀` past `η₀`, and substitute
  -- `φ₀ (ψ₀ T) = T + δ₀ (h₀ T) + h₀ (δ₀ T)`.
  rw [eq_sub_of_add_eq (sub_eq_iff_eq_add'.1 hψ).symm, map_sub, map_add, ← hφη,
    eq_add_of_sub_eq' hid, map_sub]
  abel

end Homotopy

section Cohomology

variable [DecidableEq S₀] [DecidableEq T₁] [DecidableEq T₂]
  {d₁ : S₁ → ℤ} {d₂ : S₂ → ℤ} {d₀ : S₀ → ℤ} {e₁ : T₁ → ℤ} {e₂ : T₂ → ℤ} {e₀ : T₀ → ℤ} {ε : ℤ}
  {δ₁ : S₁ → S₁ → R} {δ₂ : S₂ → S₂ → R} {η₁ : T₁ → T₁ → R} {η₂ : T₂ → T₂ → R}
  {E₁ E₂ E₁' E₂' : ℝ}
  (hδ₁ : ∀ p p', δ₁ p p' ≠ 0 → F₁ p' ≤ F₁ p + E₁) (hδ₁fin : ∀ p, δ₁ p ∈ NovikovModule R F₁)
  (hδ₂ : ∀ p p', δ₂ p p' ≠ 0 → F₂ p' ≤ F₂ p + E₂) (hδ₂fin : ∀ p, δ₂ p ∈ NovikovModule R F₂)
  (hη₁ : ∀ t t', η₁ t t' ≠ 0 → G₁ t' ≤ G₁ t + E₁') (hη₁fin : ∀ t, η₁ t ∈ NovikovModule R G₁)
  (hη₂ : ∀ t t', η₂ t t' ≠ 0 → G₂ t' ≤ G₂ t + E₂') (hη₂fin : ∀ t, η₂ t ∈ NovikovModule R G₂)
  {hndeg : ∀ {i j : ℤ} {a : NovikovModule R F₁} {b : NovikovModule R F₂},
    a ∈ gradeBy R F₁ d₁ i → b ∈ gradeBy R F₂ d₂ j →
      kernelProduct hn hfin a b ∈ gradeBy R F₀ d₀ (i + j + ε)}
  {hnL : ∀ {i : ℤ} {a : NovikovModule R F₁}, a ∈ gradeBy R F₁ d₁ i → ∀ b,
    kernelMap hδ₀ hδ₀fin (kernelProduct hn hfin a b) =
      kernelProduct hn hfin (kernelMap hδ₁ hδ₁fin a) b +
        negOnePowCast R i • kernelProduct hn hfin a (kernelMap hδ₂ hδ₂fin b)}
  {hqdeg : ∀ {i j : ℤ} {a : NovikovModule R G₁} {b : NovikovModule R G₂},
    a ∈ gradeBy R G₁ e₁ i → b ∈ gradeBy R G₂ e₂ j →
      kernelProduct hq hqfin a b ∈ gradeBy R G₀ e₀ (i + j + ε)}
  {hqL : ∀ {i : ℤ} {a : NovikovModule R G₁}, a ∈ gradeBy R G₁ e₁ i → ∀ b,
    kernelMap hη₀ hη₀fin (kernelProduct hq hqfin a b) =
      kernelProduct hq hqfin (kernelMap hη₁ hη₁fin a) b +
        negOnePowCast R i • kernelProduct hq hqfin a (kernelMap hη₂ hη₂fin b)}
  {hφ₁deg : ∀ {i : ℤ} {a : NovikovModule R G₁}, a ∈ gradeBy R G₁ e₁ i →
    kernelMap hφ₁ hφ₁fin a ∈ gradeBy R F₁ d₁ i}
  {hφ₁D : ∀ {i : ℤ} {a : NovikovModule R G₁}, a ∈ gradeBy R G₁ e₁ i →
    kernelMap hδ₁ hδ₁fin (kernelMap hφ₁ hφ₁fin a) = kernelMap hφ₁ hφ₁fin (kernelMap hη₁ hη₁fin a)}
  {hφ₂deg : ∀ {i : ℤ} {a : NovikovModule R G₂}, a ∈ gradeBy R G₂ e₂ i →
    kernelMap hφ₂ hφ₂fin a ∈ gradeBy R F₂ d₂ i}
  {hφ₂D : ∀ {i : ℤ} {a : NovikovModule R G₂}, a ∈ gradeBy R G₂ e₂ i →
    kernelMap hδ₂ hδ₂fin (kernelMap hφ₂ hφ₂fin a) = kernelMap hφ₂ hφ₂fin (kernelMap hη₂ hη₂fin a)}
  {hφ₀deg : ∀ {i : ℤ} {a : NovikovModule R G₀}, a ∈ gradeBy R G₀ e₀ i →
    kernelMap hφ₀ hφ₀fin a ∈ gradeBy R F₀ d₀ i}
  {hφ₀D : ∀ {i : ℤ} {a : NovikovModule R G₀}, a ∈ gradeBy R G₀ e₀ i →
    kernelMap hδ₀ hδ₀fin (kernelMap hφ₀ hφ₀fin a) =
      kernelMap hφ₀ hφ₀fin (kernelMap hη₀ hη₀fin a)}

variable (hndeg hnL hφ₁deg hφ₁D hφ₂deg hφ₂D hφ₀deg hφ₀D) in
include hψ₀ hψ₀fin hk hkfin hh₀ hh₀fin hη₀ hη₀fin hndeg hnL hφ₁deg hφ₁D hφ₂deg hφ₂D hφ₀deg hφ₀D in
/-- **Comparison along the chain maps, on cocycles.** Under the kernel homotopies of
`NovikovModule.kernelProduct_kernelMap_sub_kernelMap_kernelProduct`, for the Koszul tensor
differential `D = η₁ ⊗ 1 + (-1)^(e₁) ⊗ η₂`, suppose that the product `⋆` obeys the Leibniz rule
and shifts degree by `ε`, that `φ₁`, `φ₂`, `φ₀` preserve degrees and commute with the
differentials, and that `h₀` lowers degree by one. Then for cocycles `a` and `b` of degrees `i`
and `j`, the difference `φ₁ a ⋆ φ₂ b - φ₀ (a ⋆_q b)` is a coboundary of degree `i + j + ε`. -/
theorem kernelProduct_kernelMap_sub_kernelMap_kernelProduct_mem_coboundaries
    (hkd : ∀ (t : T₁ × T₂) t₀, k t t₀ ≠ 0 → e₀ t₀ = e₁ t.1 + e₂ t.2 + (ε - 1))
    (hh₀d : ∀ p p', h₀ p p' ≠ 0 → d₀ p' = d₀ p - 1)
    (hcomp : ∀ (t : T₁ × T₂) t₀,
      kernelComp (kernelComp (kernelTensor φ₁ φ₂) fun p : S₁ × S₂ => n p.1 p.2) ψ₀ t t₀ -
          q t.1 t.2 t₀ =
        kernelComp k η₀ t t₀ + kernelComp (tensorDifferential e₁ η₁ η₂) k t t₀)
    (hinv : ∀ p p', kernelComp ψ₀ φ₀ p p' - (if p = p' then 1 else 0) =
      kernelComp h₀ δ₀ p p' + kernelComp δ₀ h₀ p p')
    {i j : ℤ} {a : NovikovModule R G₁}
    (ha : a ∈ (kernelMap hη₁ hη₁fin).cocycles (gradeBy R G₁ e₁) i)
    {b : NovikovModule R G₂} (hb : b ∈ (kernelMap hη₂ hη₂fin).cocycles (gradeBy R G₂ e₂) j) :
    kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b) -
        kernelMap hφ₀ hφ₀fin (kernelProduct hq hqfin a b) ∈
      (kernelMap hδ₀ hδ₀fin).coboundaries (gradeBy R F₀ d₀) (i + j + ε) := by
  rw [LinearMap.mem_cocycles_iff] at ha hb
  have hD (t t' : T₁ × T₂) (h : tensorDifferential e₁ η₁ η₂ t t' ≠ 0) :=
    potential_le_of_tensorDifferential_ne_zero hη₁ hη₂ h
  have hDfin := tensorDifferential_mem (d₁ := e₁) hη₁fin hη₂fin
  -- The tensor product of two cocycles is a cocycle.
  have hx : kernelMap hD hDfin (tensor a b) = 0 := by
    rw [kernelMap_tensorDifferential_tensor hη₁ hη₁fin hη₂ hη₂fin hD hDfin ha.2, ha.1, hb.1]
    simp
  -- The product of the images of two cocycles is a cocycle.
  have hT : kernelMap hδ₀ hδ₀fin
      (kernelProduct hn hfin (kernelMap hφ₁ hφ₁fin a) (kernelMap hφ₂ hφ₂fin b)) = 0 := by
    rw [hnL (hφ₁deg ha.2), hφ₁D ha.2, hφ₂D hb.2, ha.1, hb.1]
    simp
  rw [kernelProduct_kernelMap_sub_kernelMap_kernelProduct hn hfin hq hqfin hφ₁ hφ₁fin hφ₂ hφ₂fin
      hφ₀ hφ₀fin hψ₀ hψ₀fin hk hkfin hh₀ hh₀fin hδ₀ hδ₀fin hη₀ hη₀fin hD hDfin hkd hφ₀D hcomp hinv
      ha.2 hb.2, hx, hT]
  simp only [map_zero, sub_self, add_zero]
  refine LinearMap.mem_coboundaries_iff.2 ⟨_, Submodule.sub_mem _ ?_ ?_, rfl⟩
  · have hdeg : i + j + (ε - 1) = i + j + ε - 1 := by ring
    exact hdeg ▸ hφ₀deg (kernelMap_mem_gradeBy hk hkfin
      (d₁ := fun t : T₁ × T₂ => e₁ t.1 + e₂ t.2) hkd (tensor_mem_gradeBy ha.2 hb.2))
  · simpa only [sub_eq_add_neg] using kernelMap_mem_gradeBy hh₀ hh₀fin
      (fun p p' h => by rw [hh₀d p p' h, sub_eq_add_neg]) (hndeg (hφ₁deg ha.2) (hφ₂deg hb.2))

include hψ₀ hψ₀fin hk hkfin hh₀ hh₀fin in
/-- **Multiplicativity on cohomology.** Let `⋆` and `⋆_q` be products obeying the Leibniz rule and
shifting degree by `ε`, so that they induce products on degree-wise cohomology, and let `φ₁`,
`φ₂`, `φ₀` be degree-preserving kernel maps commuting with the differentials, so that they induce
maps on cohomology. Suppose that a kernel `k` of degree `ε - 1` is a kernel homotopy,

`∑ₚ (φ₁ ⊗ φ₂)(t, p) ∑ₛ n(p₁, p₂, s) ψ₀(s, t₀) - q(t₁, t₂, t₀) = (k η₀ + D k)(t, t₀)`,

for the tensor differential `D = η₁ ⊗ 1 + (-1)^(e₁) ⊗ η₂` and a kernel `ψ₀` back from the output of
`⋆`, and that a kernel `h₀` lowering degree by one is a kernel homotopy
`φ₀ ψ₀ - 1 = δ₀ h₀ + h₀ δ₀`. Then the induced maps intertwine the products on cohomology:
`φ₀ (x ⋆_q y) = φ₁ x ⋆ φ₂ y` for all classes `x` of degree `i` and `y` of degree `j`. -/
theorem cohomologyMap_cohomologyProduct_kernelProduct_of_homotopy_inverse
    (hkd : ∀ (t : T₁ × T₂) t₀, k t t₀ ≠ 0 → e₀ t₀ = e₁ t.1 + e₂ t.2 + (ε - 1))
    (hh₀d : ∀ p p', h₀ p p' ≠ 0 → d₀ p' = d₀ p - 1)
    (hcomp : ∀ (t : T₁ × T₂) t₀,
      kernelComp (kernelComp (kernelTensor φ₁ φ₂) fun p : S₁ × S₂ => n p.1 p.2) ψ₀ t t₀ -
          q t.1 t.2 t₀ =
        kernelComp k η₀ t t₀ + kernelComp (tensorDifferential e₁ η₁ η₂) k t t₀)
    (hinv : ∀ p p', kernelComp ψ₀ φ₀ p p' - (if p = p' then 1 else 0) =
      kernelComp h₀ δ₀ p p' + kernelComp δ₀ h₀ p p')
    {i j l : ℤ} (hl : i + j + ε = l)
    (x : (kernelMap hη₁ hη₁fin).cohomology (gradeBy R G₁ e₁) i)
    (y : (kernelMap hη₂ hη₂fin).cohomology (gradeBy R G₂ e₂) j) :
    LinearMap.cohomologyMap (kernelMap hφ₀ hφ₀fin) hφ₀deg hφ₀D l
        (LinearMap.cohomologyProduct (kernelProduct hq hqfin) hqdeg hqL hl x y) =
      LinearMap.cohomologyProduct (kernelProduct hn hfin) hndeg hnL hl
        (LinearMap.cohomologyMap (kernelMap hφ₁ hφ₁fin) hφ₁deg hφ₁D i x)
        (LinearMap.cohomologyMap (kernelMap hφ₂ hφ₂fin) hφ₂deg hφ₂D j y) := by
  subst hl
  refine LinearMap.cohomologyMap_cohomologyProduct rfl (fun ha hb => ?_) x y
  rw [← neg_sub]
  exact Submodule.neg_mem _
    (kernelProduct_kernelMap_sub_kernelMap_kernelProduct_mem_coboundaries hn hfin hq hqfin hφ₁
      hφ₁fin hφ₂ hφ₂fin hφ₀ hφ₀fin hψ₀ hψ₀fin hk hkfin hh₀ hh₀fin hδ₀ hδ₀fin hη₀ hη₀fin hδ₁ hδ₁fin
      hδ₂ hδ₂fin hη₁ hη₁fin hη₂ hη₂fin hndeg hnL hφ₁deg hφ₁D hφ₂deg hφ₂D hφ₀deg hφ₀D hkd hh₀d
      hcomp hinv ha hb)

end Cohomology

end NovikovModule

end TauCeti
